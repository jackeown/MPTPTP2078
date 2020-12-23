%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:00 EST 2020

% Result     : CounterSatisfiable 2.08s
% Output     : Model 2.08s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Negative definition of r1_lattice3 
fof(lit_def,axiom,(
    ! [X0_43,X0_45,X0_44] :
      ( ~ r1_lattice3(X0_43,X0_45,X0_44)
    <=> ( ( X0_43 = sK1
          & X0_45 = k4_waybel_0(sK1,sK2) )
        | ( X0_43 = sK1
          & X0_45 = k4_waybel_0(sK1,sK2)
          & X0_44 = sK3 )
        | ? [X1_44] :
            ( X0_43 = sK1
            & X0_45 = k1_tarski(X1_44) ) ) ) )).

%------ Positive definition of r1_orders_2 
fof(lit_def_001,axiom,(
    ! [X0_43,X0_44,X1_44] :
      ( r1_orders_2(X0_43,X0_44,X1_44)
    <=> $false ) )).

%------ Negative definition of m1_subset_1 
fof(lit_def_002,axiom,(
    ! [X0_45,X0] :
      ( ~ m1_subset_1(X0_45,X0)
    <=> $false ) )).

%------ Positive definition of r2_lattice3 
fof(lit_def_003,axiom,(
    ! [X0_43,X0_45,X0_44] :
      ( r2_lattice3(X0_43,X0_45,X0_44)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.08/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.00  
% 2.08/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/1.00  
% 2.08/1.00  ------  iProver source info
% 2.08/1.00  
% 2.08/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.08/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/1.00  git: non_committed_changes: false
% 2.08/1.00  git: last_make_outside_of_git: false
% 2.08/1.00  
% 2.08/1.00  ------ 
% 2.08/1.00  ------ Parsing...
% 2.08/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/1.00  
% 2.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.08/1.00  
% 2.08/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/1.00  ------ Proving...
% 2.08/1.00  ------ Problem Properties 
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  clauses                                 12
% 2.08/1.00  conjectures                             3
% 2.08/1.00  EPR                                     0
% 2.08/1.00  Horn                                    9
% 2.08/1.00  unary                                   1
% 2.08/1.00  binary                                  2
% 2.08/1.00  lits                                    42
% 2.08/1.00  lits eq                                 0
% 2.08/1.00  fd_pure                                 0
% 2.08/1.00  fd_pseudo                               0
% 2.08/1.00  fd_cond                                 0
% 2.08/1.00  fd_pseudo_cond                          0
% 2.08/1.00  AC symbols                              0
% 2.08/1.00  
% 2.08/1.00  ------ Input Options Time Limit: Unbounded
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  ------ 
% 2.08/1.00  Current options:
% 2.08/1.00  ------ 
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  ------ Proving...
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 2.08/1.00  
% 2.08/1.00  ------ Building Model...Done
% 2.08/1.00  
% 2.08/1.00  %------ The model is defined over ground terms (initial term algebra).
% 2.08/1.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 2.08/1.00  %------ where \phi is a formula over the term algebra.
% 2.08/1.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 2.08/1.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 2.08/1.00  %------ See help for --sat_out_model for different model outputs.
% 2.08/1.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 2.08/1.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 2.08/1.00  % SZS output start Model for theBenchmark.p
% 2.08/1.00  
% 2.08/1.00  %------ Negative definition of r1_lattice3 
% 2.08/1.00  fof(lit_def,axiom,
% 2.08/1.00      (! [X0_43,X0_45,X0_44] : 
% 2.08/1.00        ( ~(r1_lattice3(X0_43,X0_45,X0_44)) <=>
% 2.08/1.00             (
% 2.08/1.00                (
% 2.08/1.00                  ( X0_43=sK1 & X0_45=k4_waybel_0(sK1,sK2) )
% 2.08/1.00                )
% 2.08/1.00  
% 2.08/1.00               | 
% 2.08/1.00                (
% 2.08/1.00                  ( X0_43=sK1 & X0_45=k4_waybel_0(sK1,sK2) & X0_44=sK3 )
% 2.08/1.00                )
% 2.08/1.00  
% 2.08/1.00               | 
% 2.08/1.00              ? [X1_44] : 
% 2.08/1.00                (
% 2.08/1.00                  ( X0_43=sK1 & X0_45=k1_tarski(X1_44) )
% 2.08/1.00                )
% 2.08/1.00  
% 2.08/1.00             )
% 2.08/1.00        )
% 2.08/1.00      )
% 2.08/1.00     ).
% 2.08/1.00  
% 2.08/1.00  %------ Positive definition of r1_orders_2 
% 2.08/1.00  fof(lit_def,axiom,
% 2.08/1.00      (! [X0_43,X0_44,X1_44] : 
% 2.08/1.00        ( r1_orders_2(X0_43,X0_44,X1_44) <=>
% 2.08/1.00            $false
% 2.08/1.00        )
% 2.08/1.00      )
% 2.08/1.00     ).
% 2.08/1.00  
% 2.08/1.00  %------ Negative definition of m1_subset_1 
% 2.08/1.00  fof(lit_def,axiom,
% 2.08/1.00      (! [X0_45,X0] : 
% 2.08/1.00        ( ~(m1_subset_1(X0_45,X0)) <=>
% 2.08/1.00            $false
% 2.08/1.00        )
% 2.08/1.00      )
% 2.08/1.00     ).
% 2.08/1.00  
% 2.08/1.00  %------ Positive definition of r2_lattice3 
% 2.08/1.00  fof(lit_def,axiom,
% 2.08/1.00      (! [X0_43,X0_45,X0_44] : 
% 2.08/1.00        ( r2_lattice3(X0_43,X0_45,X0_44) <=>
% 2.08/1.00            $false
% 2.08/1.00        )
% 2.08/1.00      )
% 2.08/1.00     ).
% 2.08/1.00  % SZS output end Model for theBenchmark.p
% 2.08/1.00  ------                               Statistics
% 2.08/1.00  
% 2.08/1.00  ------ Selected
% 2.08/1.00  
% 2.08/1.00  total_time:                             0.042
% 2.08/1.00  
%------------------------------------------------------------------------------
