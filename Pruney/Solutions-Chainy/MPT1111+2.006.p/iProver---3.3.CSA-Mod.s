%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:29 EST 2020

% Result     : CounterSatisfiable 3.88s
% Output     : Model 3.88s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :  103 ( 103 expanded)
%              Number of equality atoms :   89 (  89 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & X0 != k4_ordinal1
          & ( X0 != sK4
            | X1 != arAF0_k1_struct_0_0 )
          & X0 != arAF0_k1_struct_0_0
          & ( X0 != arAF0_k1_struct_0_0
            | X1 != sK4 )
          & X0 != arAF0_sK0_0
          & X0 != arAF0_k1_funct_1_0
          & X1 != k4_ordinal1
          & X1 != arAF0_k1_struct_0_0
          & X1 != arAF0_sK0_0
          & X1 != arAF0_k1_funct_1_0 )
        | ( X0_0 = $i
          & X0 = o_0_0_xboole_0
          & X1 != k4_ordinal1
          & X1 != arAF0_k1_struct_0_0
          & X1 != arAF0_sK0_0
          & X1 != arAF0_k1_funct_1_0 )
        | ( X0_0 = $i
          & X1 = X0 ) ) ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> ( ( X0 = o_0_0_xboole_0
          & X1 = k4_ordinal1 )
        | ( X0 = arAF0_sK0_0
          & X1 = k4_ordinal1 )
        | ( X0 = arAF0_sK0_0
          & X1 = arAF0_k1_struct_0_0 )
        | ( X0 = arAF0_sK0_0
          & X1 = arAF0_sK0_0 )
        | ( X0 = arAF0_sK0_0
          & X1 = arAF0_k1_funct_1_0 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = k4_ordinal1 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = arAF0_k1_struct_0_0 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = arAF0_sK0_0 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = arAF0_k1_funct_1_0 )
        | ( X1 = k4_ordinal1
          & X0 != o_0_0_xboole_0
          & X0 != k4_ordinal1
          & X0 != arAF0_k1_struct_0_0 ) ) ) )).

%------ Positive definition of m1_subset_1 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
    <=> ( ( X0 != k4_ordinal1
          & ( X0 != k4_ordinal1
            | X1 != arAF0_k9_setfam_1_0 )
          & X0 != arAF0_k1_struct_0_0
          & ( X0 != arAF0_k1_struct_0_0
            | X1 != arAF0_k9_setfam_1_0 )
          & X0 != arAF0_sK0_0
          & ( X0 != arAF0_sK0_0
            | X1 != arAF0_k9_setfam_1_0 )
          & X0 != arAF0_k1_funct_1_0
          & ( X0 != arAF0_k1_funct_1_0
            | X1 != arAF0_k9_setfam_1_0 )
          & X1 != arAF0_k1_struct_0_0
          & X1 != arAF0_sK0_0
          & X1 != arAF0_k1_funct_1_0 )
        | ( X0 = sK4
          & X1 = arAF0_k9_setfam_1_0 )
        | ( X0 = arAF0_sK1_0
          & X1 = arAF0_k9_setfam_1_0 )
        | ( X0 = arAF0_sK0_0
          & X1 = k4_ordinal1 )
        | ( X0 = arAF0_sK0_0
          & X1 = arAF0_k1_struct_0_0 )
        | ( X0 = arAF0_sK0_0
          & X1 = arAF0_sK0_0 )
        | ( X0 = arAF0_sK0_0
          & X1 = arAF0_k1_funct_1_0 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = k4_ordinal1 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = arAF0_k1_struct_0_0 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = arAF0_sK0_0 )
        | ( X0 = arAF0_k1_funct_1_0
          & X1 = arAF0_k1_funct_1_0 )
        | ( X1 = k4_ordinal1
          & X0 != k4_ordinal1
          & X0 != arAF0_k1_struct_0_0
          & X0 != arAF0_sK0_0
          & X0 != arAF0_k1_funct_1_0 ) ) ) )).

%------ Negative definition of v1_xboole_0 
fof(lit_def_003,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
    <=> ( X0 = k4_ordinal1
        | X0 = arAF0_k1_struct_0_0
        | X0 = arAF0_sK0_0
        | X0 = arAF0_k1_funct_1_0 ) ) )).

%------ Positive definition of arAF0_v1_funct_2_0 
fof(lit_def_004,axiom,
    ( arAF0_v1_funct_2_0
  <=> $true )).

%------ Positive definition of arAF0_v1_funct_1_0 
fof(lit_def_005,axiom,
    ( arAF0_v1_funct_1_0
  <=> $true )).

%------ Positive definition of arAF0_r1_tarski_0 
fof(lit_def_006,axiom,
    ( arAF0_r1_tarski_0
  <=> $true )).

%------ Positive definition of arAF0_v4_ordinal1_0 
fof(lit_def_007,axiom,
    ( arAF0_v4_ordinal1_0
  <=> $true )).

%------ Positive definition of arAF0_v3_ordinal1_0 
fof(lit_def_008,axiom,
    ( arAF0_v3_ordinal1_0
  <=> $true )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.88/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/1.01  
% 3.88/1.01  ------  iProver source info
% 3.88/1.01  
% 3.88/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.88/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/1.01  git: non_committed_changes: false
% 3.88/1.01  git: last_make_outside_of_git: false
% 3.88/1.01  
% 3.88/1.01  ------ 
% 3.88/1.01  ------ Parsing...
% 3.88/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.01  ------ Proving...
% 3.88/1.01  ------ Problem Properties 
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  clauses                                 22
% 3.88/1.01  conjectures                             3
% 3.88/1.01  EPR                                     8
% 3.88/1.01  Horn                                    15
% 3.88/1.01  unary                                   8
% 3.88/1.01  binary                                  2
% 3.88/1.01  lits                                    60
% 3.88/1.01  lits eq                                 7
% 3.88/1.01  fd_pure                                 0
% 3.88/1.01  fd_pseudo                               0
% 3.88/1.01  fd_cond                                 6
% 3.88/1.01  fd_pseudo_cond                          0
% 3.88/1.01  AC symbols                              0
% 3.88/1.01  
% 3.88/1.01  ------ Input Options Time Limit: Unbounded
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing...
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.88/1.01  Current options:
% 3.88/1.01  ------ 
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Proving...
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.01  
% 3.88/1.01  ------ Proving...
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing...
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.01  
% 3.88/1.01  ------ Proving...
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.01  
% 3.88/1.01  ------ Proving...
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.01  
% 3.88/1.01  ------ Proving...
% 3.88/1.01  
% 3.88/1.01  
% 3.88/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  ------ Building Model...Done
% 3.88/1.01  
% 3.88/1.01  %------ The model is defined over ground terms (initial term algebra).
% 3.88/1.01  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 3.88/1.01  %------ where \phi is a formula over the term algebra.
% 3.88/1.01  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 3.88/1.01  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 3.88/1.01  %------ See help for --sat_out_model for different model outputs.
% 3.88/1.01  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 3.88/1.01  %------ where the first argument stands for the sort ($i in the unsorted case)
% 3.88/1.01  % SZS output start Model for theBenchmark.p
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of equality_sorted 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01      (! [X0_0,X0_2,X1_2] : 
% 3.88/1.01        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 3.88/1.01             (
% 3.88/1.01                (
% 3.88/1.01                  ( X0_0=$o & X1_2=X0_2 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0_0=$i )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=sK4 | X1!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_struct_0_0 | X1!=sK4 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_sK0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_funct_1_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_sK0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0_0=$i & X0=o_0_0_xboole_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_sK0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0_0=$i & X1=X0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01             )
% 3.88/1.01        )
% 3.88/1.01      )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of r2_hidden 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01      (! [X0,X1] : 
% 3.88/1.01        ( r2_hidden(X0,X1) <=>
% 3.88/1.01             (
% 3.88/1.01                (
% 3.88/1.01                  ( X0=o_0_0_xboole_0 & X1=k4_ordinal1 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=k4_ordinal1 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=arAF0_k1_struct_0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=arAF0_sK0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=k4_ordinal1 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=arAF0_k1_struct_0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=arAF0_sK0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X1=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=o_0_0_xboole_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_struct_0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01             )
% 3.88/1.01        )
% 3.88/1.01      )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of m1_subset_1 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01      (! [X0,X1] : 
% 3.88/1.01        ( m1_subset_1(X0,X1) <=>
% 3.88/1.01             (
% 3.88/1.01                (
% 3.88/1.01                  ( X0!=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=k4_ordinal1 | X1!=arAF0_k9_setfam_1_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_struct_0_0 | X1!=arAF0_k9_setfam_1_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_sK0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_sK0_0 | X1!=arAF0_k9_setfam_1_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_funct_1_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_funct_1_0 | X1!=arAF0_k9_setfam_1_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_sK0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X1!=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=sK4 & X1=arAF0_k9_setfam_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK1_0 & X1=arAF0_k9_setfam_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=k4_ordinal1 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=arAF0_k1_struct_0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=arAF0_sK0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 & X1=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=k4_ordinal1 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=arAF0_k1_struct_0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=arAF0_sK0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 & X1=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X1=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=k4_ordinal1 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_struct_0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_sK0_0 )
% 3.88/1.01                 &
% 3.88/1.01                  ( X0!=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01             )
% 3.88/1.01        )
% 3.88/1.01      )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Negative definition of v1_xboole_0 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01      (! [X0] : 
% 3.88/1.01        ( ~(v1_xboole_0(X0)) <=>
% 3.88/1.01             (
% 3.88/1.01                (
% 3.88/1.01                  ( X0=k4_ordinal1 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_struct_0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_sK0_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01               | 
% 3.88/1.01                (
% 3.88/1.01                  ( X0=arAF0_k1_funct_1_0 )
% 3.88/1.01                )
% 3.88/1.01  
% 3.88/1.01             )
% 3.88/1.01        )
% 3.88/1.01      )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of arAF0_v1_funct_2_0 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01        ( arAF0_v1_funct_2_0 <=>
% 3.88/1.01            $true
% 3.88/1.01        )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of arAF0_v1_funct_1_0 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01        ( arAF0_v1_funct_1_0 <=>
% 3.88/1.01            $true
% 3.88/1.01        )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of arAF0_r1_tarski_0 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01        ( arAF0_r1_tarski_0 <=>
% 3.88/1.01            $true
% 3.88/1.01        )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of arAF0_v4_ordinal1_0 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01        ( arAF0_v4_ordinal1_0 <=>
% 3.88/1.01            $true
% 3.88/1.01        )
% 3.88/1.01     ).
% 3.88/1.01  
% 3.88/1.01  %------ Positive definition of arAF0_v3_ordinal1_0 
% 3.88/1.01  fof(lit_def,axiom,
% 3.88/1.01        ( arAF0_v3_ordinal1_0 <=>
% 3.88/1.01            $true
% 3.88/1.01        )
% 3.88/1.01     ).
% 3.88/1.01  % SZS output end Model for theBenchmark.p
% 3.88/1.01  ------                               Statistics
% 3.88/1.01  
% 3.88/1.01  ------ Selected
% 3.88/1.01  
% 3.88/1.01  total_time:                             0.457
% 3.88/1.01  
%------------------------------------------------------------------------------
