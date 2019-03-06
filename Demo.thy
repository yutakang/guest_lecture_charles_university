(*  Title:      Demo.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Download PSL at https://github.com/data61/PSL/releases/tag/v0.1.2-alpha
*)
theory Demo
imports Main (*"PSL/PSL"*)
begin

lemma demo1: "A \<and> B \<longrightarrow> (C \<longrightarrow> A \<and> C)"
  oops

lemma demo2: "w \<and> x \<longrightarrow> y \<and> z \<longrightarrow> z"
  oops

fun sep::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

(*strategy DInd = Thens [Dynamic (Induct), Auto, IsSolved]*)

lemma "map f (sep x xs) = sep (f x) (map f xs)"
  find_theorems name:"map" name:"List.list" "map _ _ = _"
(*  find_proof DInd
    try_hard *)
  oops

primrec itrev:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs [] = rev xs"
  oops

end