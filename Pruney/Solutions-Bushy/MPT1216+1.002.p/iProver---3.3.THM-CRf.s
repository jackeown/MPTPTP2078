%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1216+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:10 EST 2020

% Result     : Theorem 38.90s
% Output     : CNFRefutation 38.90s
% Verified   : 
% Statistics : Number of formulae       :  445 (17048 expanded)
%              Number of clauses        :  324 (4209 expanded)
%              Number of leaves         :   29 (4348 expanded)
%              Depth                    :   29
%              Number of atoms          : 1733 (122938 expanded)
%              Number of equality atoms :  501 (23702 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f83,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f84,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
            | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
          & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
            | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,sK7))
          | k4_lattices(X0,X1,sK7) != k5_lattices(X0) )
        & ( r3_lattices(X0,X1,k7_lattices(X0,sK7))
          | k4_lattices(X0,X1,sK7) = k5_lattices(X0) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_lattices(X0,sK6,k7_lattices(X0,X2))
              | k4_lattices(X0,sK6,X2) != k5_lattices(X0) )
            & ( r3_lattices(X0,sK6,k7_lattices(X0,X2))
              | k4_lattices(X0,sK6,X2) = k5_lattices(X0) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK5,X1,k7_lattices(sK5,X2))
                | k4_lattices(sK5,X1,X2) != k5_lattices(sK5) )
              & ( r3_lattices(sK5,X1,k7_lattices(sK5,X2))
                | k4_lattices(sK5,X1,X2) = k5_lattices(sK5) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l3_lattices(sK5)
      & v17_lattices(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,
    ( ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
      | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) )
    & ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) )
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l3_lattices(sK5)
    & v17_lattices(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f84,f87,f86,f85])).

fof(f133,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f88])).

fof(f132,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f88])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f128,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f88])).

fof(f131,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f88])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f27])).

fof(f91,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f118,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f129,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f88])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f70])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f74,f73,f72])).

fof(f102,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f31])).

fof(f98,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,(
    v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f88])).

fof(f90,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f119,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f29])).

fof(f96,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f93,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f92,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f88])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f115,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f78,f80,f79])).

fof(f109,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f135,plain,
    ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2016,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_2346,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2015,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_2347,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1785,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_46])).

cnf(c_1786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1785])).

cnf(c_43,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1790,plain,
    ( m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1786,c_43])).

cnf(c_1791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1790])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | m1_subset_1(k7_lattices(sK5,X0_61),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1791])).

cnf(c_2364,plain,
    ( m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k7_lattices(sK5,X0_61),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_1093,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_897])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_1093])).

cnf(c_45,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1283,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1094,c_45])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X1,X0) = k4_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1283])).

cnf(c_1288,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X1,X0) = k4_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1284,c_46,c_43])).

cnf(c_2010,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | k2_lattices(sK5,X1_61,X0_61) = k4_lattices(sK5,X1_61,X0_61) ),
    inference(subtyping,[status(esa)],[c_1288])).

cnf(c_2352,plain,
    ( k2_lattices(sK5,X0_61,X1_61) = k4_lattices(sK5,X0_61,X1_61)
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_2826,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,X0_61),X1_61) = k4_lattices(sK5,k7_lattices(sK5,X0_61),X1_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_2352])).

cnf(c_9334,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),X0_61) = k4_lattices(sK5,k7_lattices(sK5,sK6),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2826])).

cnf(c_9596,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),sK7) = k4_lattices(sK5,k7_lattices(sK5,sK6),sK7) ),
    inference(superposition,[status(thm)],[c_2346,c_9334])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_25])).

cnf(c_921,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_1743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_921,c_46])).

cnf(c_1744,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X1,X0),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1743])).

cnf(c_1748,plain,
    ( m1_subset_1(k2_lattices(sK5,X1,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1744,c_43])).

cnf(c_1749,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X1,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1748])).

cnf(c_2000,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X1_61,X0_61),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1749])).

cnf(c_2362,plain,
    ( m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k2_lattices(sK5,X1_61,X0_61),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_9617,plain,
    ( m1_subset_1(k4_lattices(sK5,k7_lattices(sK5,sK6),sK7),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(k7_lattices(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9596,c_2362])).

cnf(c_51,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_52,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2076,plain,
    ( m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k7_lattices(sK5,X0_61),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2078,plain,
    ( m1_subset_1(k7_lattices(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_107139,plain,
    ( m1_subset_1(k4_lattices(sK5,k7_lattices(sK5,sK6),sK7),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9617,c_51,c_52,c_2078])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_941,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_30,c_12])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_1069,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_942])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1070,c_45])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k4_lattices(sK5,X1,X0) = k4_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1304])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_lattices(sK5,X1,X0) = k4_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_46,c_43])).

cnf(c_2009,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | k4_lattices(sK5,X1_61,X0_61) = k4_lattices(sK5,X0_61,X1_61) ),
    inference(subtyping,[status(esa)],[c_1309])).

cnf(c_2353,plain,
    ( k4_lattices(sK5,X0_61,X1_61) = k4_lattices(sK5,X1_61,X0_61)
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_2927,plain,
    ( k4_lattices(sK5,X0_61,sK7) = k4_lattices(sK5,sK7,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2353])).

cnf(c_3071,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,X0_61),sK7) = k4_lattices(sK5,sK7,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_2927])).

cnf(c_12111,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK6),sK7) = k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_2347,c_3071])).

cnf(c_107143,plain,
    ( m1_subset_1(k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_107139,c_12111])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1822,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_46])).

cnf(c_1823,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_1822])).

cnf(c_9,plain,
    ( v11_lattices(X0)
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_44,negated_conjecture,
    ( v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1131,plain,
    ( v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_44])).

cnf(c_1132,plain,
    ( v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_141,plain,
    ( v11_lattices(sK5)
    | ~ v17_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1134,plain,
    ( v11_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_46,c_44,c_43,c_141])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1134])).

cnf(c_1652,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_1651])).

cnf(c_1826,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X2,X1),k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,X2,k1_lattices(sK5,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1823,c_46,c_43,c_1652])).

cnf(c_1827,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1,X2),k2_lattices(sK5,X1,X0)) = k2_lattices(sK5,X1,k1_lattices(sK5,X2,X0)) ),
    inference(renaming,[status(thm)],[c_1826])).

cnf(c_2003,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X2_61,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1_61,X2_61),k2_lattices(sK5,X1_61,X0_61)) = k2_lattices(sK5,X1_61,k1_lattices(sK5,X2_61,X0_61)) ),
    inference(subtyping,[status(esa)],[c_1827])).

cnf(c_2359,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_61,X1_61),k2_lattices(sK5,X0_61,X2_61)) = k2_lattices(sK5,X0_61,k1_lattices(sK5,X1_61,X2_61))
    | m1_subset_1(X2_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_4251,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_61),k2_lattices(sK5,sK6,X1_61)) = k2_lattices(sK5,sK6,k1_lattices(sK5,X0_61,X1_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2359])).

cnf(c_4374,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k7_lattices(sK5,X0_61)),k2_lattices(sK5,sK6,X1_61)) = k2_lattices(sK5,sK6,k1_lattices(sK5,k7_lattices(sK5,X0_61),X1_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_4251])).

cnf(c_100175,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k2_lattices(sK5,sK6,X0_61)) = k2_lattices(sK5,sK6,k1_lattices(sK5,k7_lattices(sK5,sK7),X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_4374])).

cnf(c_2823,plain,
    ( k2_lattices(sK5,sK6,X0_61) = k4_lattices(sK5,sK6,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2352])).

cnf(c_2995,plain,
    ( k2_lattices(sK5,sK6,k7_lattices(sK5,X0_61)) = k4_lattices(sK5,sK6,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_2823])).

cnf(c_11140,plain,
    ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2346,c_2995])).

cnf(c_100206,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k2_lattices(sK5,sK6,X0_61)) = k2_lattices(sK5,sK6,k1_lattices(sK5,k7_lattices(sK5,sK7),X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_100175,c_11140])).

cnf(c_119401,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k2_lattices(sK5,sK6,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)))) = k2_lattices(sK5,sK6,k1_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)))) ),
    inference(superposition,[status(thm)],[c_107143,c_100206])).

cnf(c_4038,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,X0_61,X1_61)) = k4_lattices(sK5,sK6,k2_lattices(sK5,X0_61,X1_61))
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2362,c_2823])).

cnf(c_54731,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_61)) = k4_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_4038])).

cnf(c_54790,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,k7_lattices(sK5,X0_61))) = k4_lattices(sK5,sK6,k2_lattices(sK5,sK7,k7_lattices(sK5,X0_61)))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_54731])).

cnf(c_87509,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,k7_lattices(sK5,sK6))) = k4_lattices(sK5,sK6,k2_lattices(sK5,sK7,k7_lattices(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_2347,c_54790])).

cnf(c_2822,plain,
    ( k2_lattices(sK5,sK7,X0_61) = k4_lattices(sK5,sK7,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2352])).

cnf(c_2896,plain,
    ( k2_lattices(sK5,sK7,k7_lattices(sK5,X0_61)) = k4_lattices(sK5,sK7,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_2822])).

cnf(c_10154,plain,
    ( k2_lattices(sK5,sK7,k7_lattices(sK5,sK6)) = k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_2347,c_2896])).

cnf(c_87538,plain,
    ( k2_lattices(sK5,sK6,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6))) = k4_lattices(sK5,sK6,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6))) ),
    inference(light_normalisation,[status(thm)],[c_87509,c_10154])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_31])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_29,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_644,c_29])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_662,c_45])).

cnf(c_1347,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,X1,X0) = k3_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1346])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,X1,X0) = k3_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1347,c_46,c_43])).

cnf(c_2007,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | k1_lattices(sK5,X1_61,X0_61) = k3_lattices(sK5,X1_61,X0_61) ),
    inference(subtyping,[status(esa)],[c_1351])).

cnf(c_2355,plain,
    ( k1_lattices(sK5,X0_61,X1_61) = k3_lattices(sK5,X0_61,X1_61)
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_3527,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,X0_61),X1_61) = k3_lattices(sK5,k7_lattices(sK5,X0_61),X1_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_2355])).

cnf(c_17370,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK7),X0_61) = k3_lattices(sK5,k7_lattices(sK5,sK7),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_3527])).

cnf(c_107467,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK7,k7_lattices(sK5,sK6))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK7,k7_lattices(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_107143,c_17370])).

cnf(c_119410,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k4_lattices(sK5,sK6,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)))) = k2_lattices(sK5,sK6,k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)))) ),
    inference(light_normalisation,[status(thm)],[c_119401,c_87538,c_107467])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_44])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1178])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1179,c_46,c_45,c_43])).

cnf(c_2012,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | k3_lattices(sK5,k7_lattices(sK5,X0_61),X0_61) = k6_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_1183])).

cnf(c_2350,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,X0_61),X0_61) = k6_lattices(sK5)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2012])).

cnf(c_2579,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),sK7) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_2346,c_2350])).

cnf(c_27,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_777,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_29,c_27])).

cnf(c_1718,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_777,c_46])).

cnf(c_1719,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1718])).

cnf(c_83,plain,
    ( l2_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_89,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l2_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1721,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1719,c_46,c_43,c_83,c_89])).

cnf(c_2001,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1721])).

cnf(c_2361,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_2993,plain,
    ( k2_lattices(sK5,sK6,k6_lattices(sK5)) = k4_lattices(sK5,sK6,k6_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_2361,c_2823])).

cnf(c_2928,plain,
    ( k4_lattices(sK5,X0_61,sK6) = k4_lattices(sK5,sK6,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2353])).

cnf(c_3206,plain,
    ( k4_lattices(sK5,sK6,k6_lattices(sK5)) = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(superposition,[status(thm)],[c_2361,c_2928])).

cnf(c_8,plain,
    ( ~ v17_lattices(X0)
    | v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5,plain,
    ( ~ v15_lattices(X0)
    | v14_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v15_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_36])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_582])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_1142,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_740,c_44])).

cnf(c_1143,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,k6_lattices(sK5),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1142])).

cnf(c_1147,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,k6_lattices(sK5),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1143,c_46,c_45,c_43])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | k4_lattices(sK5,k6_lattices(sK5),X0_61) = X0_61 ),
    inference(subtyping,[status(esa)],[c_1147])).

cnf(c_2348,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),X0_61) = X0_61
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_2425,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_2347,c_2348])).

cnf(c_3209,plain,
    ( k4_lattices(sK5,sK6,k6_lattices(sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_3206,c_2425])).

cnf(c_5074,plain,
    ( k2_lattices(sK5,sK6,k6_lattices(sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_2993,c_2993,c_3209])).

cnf(c_19,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_791,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_29,c_19])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_34,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_989,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_34])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_993,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_989,c_34,c_2,c_1,c_0])).

cnf(c_40,negated_conjecture,
    ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_354,plain,
    ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(prop_impl,[status(thm)],[c_40])).

cnf(c_1247,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k7_lattices(sK5,sK7) != X2
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_993,c_354])).

cnf(c_1248,plain,
    ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1247])).

cnf(c_1250,plain,
    ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1248,c_46,c_45,c_43,c_42])).

cnf(c_1404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = X0
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k7_lattices(sK5,sK7) != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_791,c_1250])).

cnf(c_1405,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1404])).

cnf(c_1407,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1405,c_46,c_43,c_42])).

cnf(c_2005,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_1407])).

cnf(c_2357,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2005])).

cnf(c_2401,plain,
    ( m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_4404,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2357,c_41,c_2005,c_2401])).

cnf(c_4405,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(renaming,[status(thm)],[c_4404])).

cnf(c_3524,plain,
    ( k1_lattices(sK5,sK6,X0_61) = k3_lattices(sK5,sK6,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2355])).

cnf(c_3640,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,X0_61)) = k3_lattices(sK5,sK6,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_3524])).

cnf(c_20014,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2346,c_3640])).

cnf(c_20182,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(superposition,[status(thm)],[c_4405,c_20014])).

cnf(c_4250,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,X0_61),k2_lattices(sK5,sK7,X1_61)) = k2_lattices(sK5,sK7,k1_lattices(sK5,X0_61,X1_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2359])).

cnf(c_4281,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,k7_lattices(sK5,X0_61)),k2_lattices(sK5,sK7,X1_61)) = k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,X0_61),X1_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_4250])).

cnf(c_91832,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,k7_lattices(sK5,sK7)),k2_lattices(sK5,sK7,X0_61)) = k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,sK7),X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_4281])).

cnf(c_12110,plain,
    ( k4_lattices(sK5,sK7,k7_lattices(sK5,sK7)) = k4_lattices(sK5,k7_lattices(sK5,sK7),sK7) ),
    inference(superposition,[status(thm)],[c_2346,c_3071])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1196,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_44])).

cnf(c_1197,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1196])).

cnf(c_1201,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1197,c_46,c_45,c_43])).

cnf(c_2011,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | k4_lattices(sK5,k7_lattices(sK5,X0_61),X0_61) = k5_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_1201])).

cnf(c_2351,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,X0_61),X0_61) = k5_lattices(sK5)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_2748,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK7),sK7) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_2346,c_2351])).

cnf(c_12120,plain,
    ( k4_lattices(sK5,sK7,k7_lattices(sK5,sK7)) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_12110,c_2748])).

cnf(c_10153,plain,
    ( k2_lattices(sK5,sK7,k7_lattices(sK5,sK7)) = k4_lattices(sK5,sK7,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2346,c_2896])).

cnf(c_13197,plain,
    ( k2_lattices(sK5,sK7,k7_lattices(sK5,sK7)) = k5_lattices(sK5) ),
    inference(demodulation,[status(thm)],[c_12120,c_10153])).

cnf(c_91863,plain,
    ( k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,sK7),X0_61)) = k1_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK7,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91832,c_13197])).

cnf(c_91957,plain,
    ( k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,sK7),sK6)) = k1_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_2347,c_91863])).

cnf(c_3068,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_2347,c_2927])).

cnf(c_2893,plain,
    ( k2_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK7,sK6) ),
    inference(superposition,[status(thm)],[c_2347,c_2822])).

cnf(c_3202,plain,
    ( k2_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(demodulation,[status(thm)],[c_3068,c_2893])).

cnf(c_17575,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k3_lattices(sK5,k7_lattices(sK5,sK7),sK6) ),
    inference(superposition,[status(thm)],[c_2347,c_17370])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_673,c_29])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_691,c_45])).

cnf(c_1326,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k3_lattices(sK5,X1,X0) = k3_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1325])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k3_lattices(sK5,X1,X0) = k3_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1326,c_46,c_43])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | k3_lattices(sK5,X1_61,X0_61) = k3_lattices(sK5,X0_61,X1_61) ),
    inference(subtyping,[status(esa)],[c_1330])).

cnf(c_2354,plain,
    ( k3_lattices(sK5,X0_61,X1_61) = k3_lattices(sK5,X1_61,X0_61)
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_3301,plain,
    ( k3_lattices(sK5,X0_61,sK6) = k3_lattices(sK5,sK6,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2354])).

cnf(c_3413,plain,
    ( k3_lattices(sK5,sK6,k7_lattices(sK5,X0_61)) = k3_lattices(sK5,k7_lattices(sK5,X0_61),sK6)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_3301])).

cnf(c_16280,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2346,c_3413])).

cnf(c_17584,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_17575,c_16280])).

cnf(c_2991,plain,
    ( k2_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_2346,c_2823])).

cnf(c_4026,plain,
    ( m1_subset_1(k4_lattices(sK5,sK6,sK7),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2991,c_2362])).

cnf(c_22718,plain,
    ( m1_subset_1(k4_lattices(sK5,sK6,sK7),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4026,c_51,c_52])).

cnf(c_26,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_882,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_30,c_26])).

cnf(c_1707,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_882,c_46])).

cnf(c_1708,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1707])).

cnf(c_80,plain,
    ( l1_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_92,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1710,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1708,c_46,c_43,c_80,c_92])).

cnf(c_2002,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1710])).

cnf(c_2360,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2002])).

cnf(c_3526,plain,
    ( k1_lattices(sK5,k5_lattices(sK5),X0_61) = k3_lattices(sK5,k5_lattices(sK5),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_2355])).

cnf(c_22748,plain,
    ( k1_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK6,sK7)) = k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_22718,c_3526])).

cnf(c_6,plain,
    ( v13_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v15_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_35])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_613])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_716,c_44])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k3_lattices(sK5,k5_lattices(sK5),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1160])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_lattices(sK5,k5_lattices(sK5),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_46,c_45,c_43])).

cnf(c_2013,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | k3_lattices(sK5,k5_lattices(sK5),X0_61) = X0_61 ),
    inference(subtyping,[status(esa)],[c_1165])).

cnf(c_2349,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),X0_61) = X0_61
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_22786,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK6,sK7)) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_22718,c_2349])).

cnf(c_22797,plain,
    ( k1_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK6,sK7)) = k4_lattices(sK5,sK6,sK7) ),
    inference(demodulation,[status(thm)],[c_22748,c_22786])).

cnf(c_91985,plain,
    ( k2_lattices(sK5,sK7,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k4_lattices(sK5,sK6,sK7) ),
    inference(light_normalisation,[status(thm)],[c_91957,c_3202,c_17584,c_22797])).

cnf(c_92136,plain,
    ( k2_lattices(sK5,sK7,k7_lattices(sK5,sK7)) = k4_lattices(sK5,sK6,sK7)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_20182,c_91985])).

cnf(c_92138,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_92136,c_13197])).

cnf(c_2825,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),X0_61) = k4_lattices(sK5,k5_lattices(sK5),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_2352])).

cnf(c_8687,plain,
    ( k2_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)) = k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_2360,c_2825])).

cnf(c_9073,plain,
    ( m1_subset_1(k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8687,c_2362])).

cnf(c_47,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_50,plain,
    ( l3_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_79,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_81,plain,
    ( l1_lattices(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_91,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_93,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top
    | l1_lattices(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_11922,plain,
    ( m1_subset_1(k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9073,c_47,c_50,c_81,c_93])).

cnf(c_9333,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK7),X0_61) = k4_lattices(sK5,k7_lattices(sK5,sK7),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2826])).

cnf(c_9498,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k4_lattices(sK5,k7_lattices(sK5,sK7),sK6) ),
    inference(superposition,[status(thm)],[c_2347,c_9333])).

cnf(c_9518,plain,
    ( m1_subset_1(k4_lattices(sK5,k7_lattices(sK5,sK7),sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9498,c_2362])).

cnf(c_2402,plain,
    ( m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2401])).

cnf(c_104215,plain,
    ( m1_subset_1(k4_lattices(sK5,k7_lattices(sK5,sK7),sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9518,c_51,c_52,c_2402])).

cnf(c_3208,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,X0_61),sK6) = k4_lattices(sK5,sK6,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_2928])).

cnf(c_14434,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k4_lattices(sK5,k7_lattices(sK5,sK7),sK6) ),
    inference(superposition,[status(thm)],[c_2346,c_3208])).

cnf(c_104219,plain,
    ( m1_subset_1(k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_104215,c_14434])).

cnf(c_104571,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),X0_61) = k3_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_104219,c_2355])).

cnf(c_105507,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5))) = k3_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5))) ),
    inference(superposition,[status(thm)],[c_11922,c_104571])).

cnf(c_11956,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),X0_61) = k3_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11922,c_2355])).

cnf(c_76333,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),k5_lattices(sK5)) = k3_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_2360,c_11956])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1803,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_46])).

cnf(c_1804,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1803])).

cnf(c_1272,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_45])).

cnf(c_1273,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1272])).

cnf(c_161,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1275,plain,
    ( v8_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1273,c_46,c_45,c_43,c_161])).

cnf(c_1501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1275])).

cnf(c_1502,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1501])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1804,c_46,c_43,c_1502])).

cnf(c_2004,plain,
    ( ~ m1_subset_1(X0_61,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_61,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1_61,X0_61),X0_61) = X0_61 ),
    inference(subtyping,[status(esa)],[c_1808])).

cnf(c_2358,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_61,X1_61),X1_61) = X1_61
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_3742,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,k5_lattices(sK5),X0_61),X0_61) = X0_61
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_2358])).

cnf(c_10661,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),k5_lattices(sK5)) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_2360,c_3742])).

cnf(c_10669,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),k5_lattices(sK5)) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_10661,c_8687])).

cnf(c_3303,plain,
    ( k3_lattices(sK5,X0_61,k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_2354])).

cnf(c_11932,plain,
    ( k3_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5))) ),
    inference(superposition,[status(thm)],[c_11922,c_3303])).

cnf(c_11968,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5))) = k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_11922,c_2349])).

cnf(c_11978,plain,
    ( k3_lattices(sK5,k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)),k5_lattices(sK5)) = k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)) ),
    inference(demodulation,[status(thm)],[c_11932,c_11968])).

cnf(c_76353,plain,
    ( k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5)) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_76333,c_10669,c_11978])).

cnf(c_104547,plain,
    ( k3_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) ),
    inference(superposition,[status(thm)],[c_104219,c_3303])).

cnf(c_4044,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,X0_61,X1_61)) = k2_lattices(sK5,X0_61,X1_61)
    | m1_subset_1(X1_61,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2362,c_2349])).

cnf(c_64017,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK6,X0_61)) = k2_lattices(sK5,sK6,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_4044])).

cnf(c_64230,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK6,k7_lattices(sK5,X0_61))) = k2_lattices(sK5,sK6,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_64017])).

cnf(c_67629,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2346,c_64230])).

cnf(c_67655,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_67629,c_11140])).

cnf(c_104593,plain,
    ( k3_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k5_lattices(sK5)) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_104547,c_67655])).

cnf(c_105512,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k5_lattices(sK5)) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_105507,c_76353,c_104593])).

cnf(c_91833,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k2_lattices(sK5,sK7,X0_61)) = k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,sK6),X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_4281])).

cnf(c_91862,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k2_lattices(sK5,sK7,X0_61)) = k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,sK6),X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91833,c_10154])).

cnf(c_119289,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k2_lattices(sK5,sK7,sK6)) = k2_lattices(sK5,sK7,k1_lattices(sK5,k7_lattices(sK5,sK6),sK6)) ),
    inference(superposition,[status(thm)],[c_2347,c_91862])).

cnf(c_2894,plain,
    ( k2_lattices(sK5,sK7,k6_lattices(sK5)) = k4_lattices(sK5,sK7,k6_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_2361,c_2822])).

cnf(c_3069,plain,
    ( k4_lattices(sK5,sK7,k6_lattices(sK5)) = k4_lattices(sK5,k6_lattices(sK5),sK7) ),
    inference(superposition,[status(thm)],[c_2361,c_2927])).

cnf(c_2424,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_2346,c_2348])).

cnf(c_3072,plain,
    ( k4_lattices(sK5,sK7,k6_lattices(sK5)) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_3069,c_2424])).

cnf(c_4921,plain,
    ( k2_lattices(sK5,sK7,k6_lattices(sK5)) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_2894,c_2894,c_3072])).

cnf(c_17371,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK6),X0_61) = k3_lattices(sK5,k7_lattices(sK5,sK6),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_3527])).

cnf(c_17597,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_2347,c_17371])).

cnf(c_2580,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_2347,c_2350])).

cnf(c_17606,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k6_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_17597,c_2580])).

cnf(c_119324,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k4_lattices(sK5,sK6,sK7)) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_119289,c_3202,c_4921,c_17606])).

cnf(c_107503,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),X0_61) = k3_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_107143,c_2355])).

cnf(c_109250,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5))) = k3_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k4_lattices(sK5,k5_lattices(sK5),k5_lattices(sK5))) ),
    inference(superposition,[status(thm)],[c_11922,c_107503])).

cnf(c_107479,plain,
    ( k3_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK7,k7_lattices(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_107143,c_3303])).

cnf(c_64016,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK7,X0_61)) = k2_lattices(sK5,sK7,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_4044])).

cnf(c_64075,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK7,k7_lattices(sK5,X0_61))) = k2_lattices(sK5,sK7,k7_lattices(sK5,X0_61))
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_64016])).

cnf(c_66251,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k2_lattices(sK5,sK7,k7_lattices(sK5,sK6))) = k2_lattices(sK5,sK7,k7_lattices(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_2347,c_64075])).

cnf(c_66275,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k4_lattices(sK5,sK7,k7_lattices(sK5,sK6))) = k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_66251,c_10154])).

cnf(c_107525,plain,
    ( k3_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k5_lattices(sK5)) = k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_107479,c_66275])).

cnf(c_109257,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)),k5_lattices(sK5)) = k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_109250,c_76353,c_107525])).

cnf(c_119325,plain,
    ( k4_lattices(sK5,sK7,k7_lattices(sK5,sK6)) = sK7 ),
    inference(demodulation,[status(thm)],[c_119324,c_92138,c_109257])).

cnf(c_119411,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6 ),
    inference(demodulation,[status(thm)],[c_119410,c_2579,c_5074,c_92138,c_105512,c_119325])).

cnf(c_3740,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_61),X0_61) = X0_61
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2358])).

cnf(c_3832,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k7_lattices(sK5,X0_61)),k7_lattices(sK5,X0_61)) = k7_lattices(sK5,X0_61)
    | m1_subset_1(X0_61,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_3740])).

cnf(c_20578,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(superposition,[status(thm)],[c_2346,c_3832])).

cnf(c_20594,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(light_normalisation,[status(thm)],[c_20578,c_11140])).

cnf(c_119452,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(demodulation,[status(thm)],[c_119411,c_20594])).

cnf(c_18,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_814,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_29,c_18])).

cnf(c_33,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1021,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_33])).

cnf(c_1025,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_33,c_2,c_1,c_0])).

cnf(c_39,negated_conjecture,
    ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_352,plain,
    ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(prop_impl,[status(thm)],[c_39])).

cnf(c_1230,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)
    | k7_lattices(sK5,sK7) != X2
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1025,c_352])).

cnf(c_1231,plain,
    ( ~ r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1230])).

cnf(c_1233,plain,
    ( ~ r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_46,c_45,c_43,c_42])).

cnf(c_1387,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) != X0
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)
    | k7_lattices(sK5,sK7) != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_814,c_1233])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1387])).

cnf(c_1390,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1388,c_46,c_43,c_42])).

cnf(c_2006,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_1390])).

cnf(c_2356,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_3589,plain,
    ( k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)
    | k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != k7_lattices(sK5,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2356,c_41,c_2006,c_2401])).

cnf(c_3590,plain,
    ( k1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != k7_lattices(sK5,sK7)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(renaming,[status(thm)],[c_3589])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_119452,c_92138,c_3590])).


%------------------------------------------------------------------------------
