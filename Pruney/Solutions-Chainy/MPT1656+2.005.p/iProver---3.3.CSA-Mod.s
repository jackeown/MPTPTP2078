%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:59 EST 2020

% Result     : CounterSatisfiable 1.86s
% Output     : Model 1.86s
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.86/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.86/0.98  
% 1.86/0.98  ------  iProver source info
% 1.86/0.98  
% 1.86/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.86/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.86/0.98  git: non_committed_changes: false
% 1.86/0.98  git: last_make_outside_of_git: false
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  ------ Parsing...
% 1.86/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.86/0.98  ------ Proving...
% 1.86/0.98  ------ Problem Properties 
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  clauses                                 12
% 1.86/0.98  conjectures                             3
% 1.86/0.98  EPR                                     0
% 1.86/0.98  Horn                                    9
% 1.86/0.98  unary                                   1
% 1.86/0.98  binary                                  2
% 1.86/0.98  lits                                    42
% 1.86/0.98  lits eq                                 0
% 1.86/0.98  fd_pure                                 0
% 1.86/0.98  fd_pseudo                               0
% 1.86/0.98  fd_cond                                 0
% 1.86/0.98  fd_pseudo_cond                          0
% 1.86/0.98  AC symbols                              0
% 1.86/0.98  
% 1.86/0.98  ------ Input Options Time Limit: Unbounded
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  Current options:
% 1.86/0.98  ------ 
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  ------ Proving...
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  ------ Building Model...Done
% 1.86/0.98  
% 1.86/0.98  %------ The model is defined over ground terms (initial term algebra).
% 1.86/0.98  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 1.86/0.98  %------ where \phi is a formula over the term algebra.
% 1.86/0.98  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 1.86/0.98  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 1.86/0.98  %------ See help for --sat_out_model for different model outputs.
% 1.86/0.98  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 1.86/0.98  %------ where the first argument stands for the sort ($i in the unsorted case)
% 1.86/0.98  % SZS output start Model for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  %------ Negative definition of r1_lattice3 
% 1.86/0.98  fof(lit_def,axiom,
% 1.86/0.98      (! [X0_43,X0_45,X0_44] : 
% 1.86/0.98        ( ~(r1_lattice3(X0_43,X0_45,X0_44)) <=>
% 1.86/0.98             (
% 1.86/0.98                (
% 1.86/0.98                  ( X0_43=sK1 & X0_45=k4_waybel_0(sK1,sK2) )
% 1.86/0.98                )
% 1.86/0.98  
% 1.86/0.98               | 
% 1.86/0.98                (
% 1.86/0.98                  ( X0_43=sK1 & X0_45=k4_waybel_0(sK1,sK2) & X0_44=sK3 )
% 1.86/0.98                )
% 1.86/0.98  
% 1.86/0.98               | 
% 1.86/0.98              ? [X1_44] : 
% 1.86/0.98                (
% 1.86/0.98                  ( X0_43=sK1 & X0_45=k1_tarski(X1_44) )
% 1.86/0.98                )
% 1.86/0.98  
% 1.86/0.98             )
% 1.86/0.98        )
% 1.86/0.98      )
% 1.86/0.98     ).
% 1.86/0.98  
% 1.86/0.98  %------ Positive definition of r1_orders_2 
% 1.86/0.98  fof(lit_def,axiom,
% 1.86/0.98      (! [X0_43,X0_44,X1_44] : 
% 1.86/0.98        ( r1_orders_2(X0_43,X0_44,X1_44) <=>
% 1.86/0.98            $false
% 1.86/0.98        )
% 1.86/0.98      )
% 1.86/0.98     ).
% 1.86/0.98  
% 1.86/0.98  %------ Negative definition of m1_subset_1 
% 1.86/0.98  fof(lit_def,axiom,
% 1.86/0.98      (! [X0_45,X0] : 
% 1.86/0.98        ( ~(m1_subset_1(X0_45,X0)) <=>
% 1.86/0.98            $false
% 1.86/0.98        )
% 1.86/0.98      )
% 1.86/0.98     ).
% 1.86/0.98  
% 1.86/0.98  %------ Positive definition of r2_lattice3 
% 1.86/0.98  fof(lit_def,axiom,
% 1.86/0.98      (! [X0_43,X0_45,X0_44] : 
% 1.86/0.98        ( r2_lattice3(X0_43,X0_45,X0_44) <=>
% 1.86/0.98            $false
% 1.86/0.98        )
% 1.86/0.98      )
% 1.86/0.98     ).
% 1.86/0.98  % SZS output end Model for theBenchmark.p
% 1.86/0.98  ------                               Statistics
% 1.86/0.98  
% 1.86/0.98  ------ Selected
% 1.86/0.98  
% 1.86/0.98  total_time:                             0.061
% 1.86/0.98  
%------------------------------------------------------------------------------
