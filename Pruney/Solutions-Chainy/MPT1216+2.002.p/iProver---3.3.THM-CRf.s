%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:22 EST 2020

% Result     : Theorem 23.57s
% Output     : CNFRefutation 23.57s
% Verified   : 
% Statistics : Number of formulae       :  445 (12419 expanded)
%              Number of clauses        :  316 (2732 expanded)
%              Number of leaves         :   30 (3344 expanded)
%              Depth                    :   29
%              Number of atoms          : 1875 (93299 expanded)
%              Number of equality atoms :  521 (18356 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,negated_conjecture,(
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
    inference(negated_conjecture,[],[f33])).

fof(f98,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f99,plain,(
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
    inference(flattening,[],[f98])).

fof(f113,plain,(
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
    inference(nnf_transformation,[],[f99])).

fof(f114,plain,(
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
    inference(flattening,[],[f113])).

fof(f117,plain,(
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

fof(f116,plain,(
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

fof(f115,plain,
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

fof(f118,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f114,f117,f116,f115])).

fof(f175,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f118])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f146,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f171,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f118])).

fof(f174,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f118])).

fof(f176,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f118])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f41])).

fof(f131,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f160,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f173,plain,(
    v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f118])).

fof(f172,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f118])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f37])).

fof(f121,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f148,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f94])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f123,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f147,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f166,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f132,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f39])).

fof(f128,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f90])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f129,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f165,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f111,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f151,plain,(
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
    inference(cnf_transformation,[],[f111])).

fof(f177,plain,
    ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f118])).

fof(f125,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f126,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f106,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f107,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f106])).

fof(f109,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) != sK3(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != sK3(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f107,f109,f108])).

fof(f140,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f96])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f152,plain,(
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
    inference(cnf_transformation,[],[f111])).

fof(f178,plain,
    ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_55,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_3492,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_59,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_2700,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_59])).

cnf(c_2701,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2700])).

cnf(c_56,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_2705,plain,
    ( m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_56])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_2705])).

cnf(c_3463,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2706])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f176])).

cnf(c_3493,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_12,plain,
    ( v11_lattices(X0)
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v17_lattices(X4)
    | ~ l3_lattices(X4)
    | ~ l3_lattices(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X4
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_41])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_57,negated_conjecture,
    ( v17_lattices(sK5) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_1968,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1062,c_57])).

cnf(c_1969,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,k3_lattices(sK5,X1,X2),k3_lattices(sK5,X1,X0)) = k3_lattices(sK5,X1,k4_lattices(sK5,X2,X0)) ),
    inference(unflattening,[status(thm)],[c_1968])).

cnf(c_58,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,k3_lattices(sK5,X1,X2),k3_lattices(sK5,X1,X0)) = k3_lattices(sK5,X1,k4_lattices(sK5,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1969,c_59,c_58,c_56])).

cnf(c_1974,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k4_lattices(sK5,k3_lattices(sK5,X2,X0),k3_lattices(sK5,X2,X1)) = k3_lattices(sK5,X2,k4_lattices(sK5,X0,X1)) ),
    inference(renaming,[status(thm)],[c_1973])).

cnf(c_3489,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,X0,X1),k3_lattices(sK5,X0,X2)) = k3_lattices(sK5,X0,k4_lattices(sK5,X1,X2))
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_7823,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,X0),X1),k3_lattices(sK5,k7_lattices(sK5,X0),X2)) = k3_lattices(sK5,k7_lattices(sK5,X0),k4_lattices(sK5,X1,X2))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3489])).

cnf(c_81268,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),X0),k3_lattices(sK5,k7_lattices(sK5,sK7),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_7823])).

cnf(c_81286,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),sK6),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_81268])).

cnf(c_6,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_807,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_28,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_807,c_28])).

cnf(c_2439,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_825,c_58])).

cnf(c_2440,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_2439])).

cnf(c_2444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2440,c_59,c_56])).

cnf(c_3469,plain,
    ( k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2444])).

cnf(c_6605,plain,
    ( k3_lattices(sK5,X0,sK6) = k3_lattices(sK5,sK6,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3469])).

cnf(c_7213,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,X0),sK6) = k3_lattices(sK5,sK6,k7_lattices(sK5,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_6605])).

cnf(c_20310,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3493,c_7213])).

cnf(c_81292,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_81286,c_20310])).

cnf(c_82017,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,k7_lattices(sK5,X0)))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_81292])).

cnf(c_99449,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,k7_lattices(sK5,sK6))) ),
    inference(superposition,[status(thm)],[c_3492,c_82017])).

cnf(c_50,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f169])).

cnf(c_2109,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_50,c_57])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_2109])).

cnf(c_2114,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2110,c_59,c_58,c_56])).

cnf(c_2115,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1)) ),
    inference(renaming,[status(thm)],[c_2114])).

cnf(c_3482,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2115])).

cnf(c_7597,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)) = k7_lattices(sK5,k4_lattices(sK5,sK7,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_3482])).

cnf(c_7619,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6)) = k7_lattices(sK5,k4_lattices(sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_3492,c_7597])).

cnf(c_4,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_29,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_29,c_15])).

cnf(c_1363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1363])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_1461])).

cnf(c_2418,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1462,c_58])).

cnf(c_2419,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_2418])).

cnf(c_2423,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2419,c_59,c_56])).

cnf(c_3470,plain,
    ( k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2423])).

cnf(c_7226,plain,
    ( k4_lattices(sK5,X0,sK7) = k4_lattices(sK5,sK7,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_3470])).

cnf(c_7248,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_3492,c_7226])).

cnf(c_7625,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6)) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_7619,c_7248])).

cnf(c_47,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_2166,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_47,c_57])).

cnf(c_2167,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2166])).

cnf(c_2171,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2167,c_59,c_58,c_56])).

cnf(c_3479,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_5855,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,X0)),k7_lattices(sK5,X0)) = k5_lattices(sK5)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3479])).

cnf(c_19481,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,sK6)),k7_lattices(sK5,sK6)) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3492,c_5855])).

cnf(c_49,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f168])).

cnf(c_2130,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_49,c_57])).

cnf(c_2131,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k7_lattices(sK5,k7_lattices(sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_2130])).

cnf(c_2135,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k7_lattices(sK5,k7_lattices(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_59,c_58,c_56])).

cnf(c_3481,plain,
    ( k7_lattices(sK5,k7_lattices(sK5,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_4829,plain,
    ( k7_lattices(sK5,k7_lattices(sK5,sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_3492,c_3481])).

cnf(c_19487,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK6)) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_19481,c_4829])).

cnf(c_25,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1229,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_29,c_25])).

cnf(c_2648,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1229,c_59])).

cnf(c_2649,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2648])).

cnf(c_133,plain,
    ( l1_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_145,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2651,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_59,c_56,c_133,c_145])).

cnf(c_3466,plain,
    ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_6607,plain,
    ( k3_lattices(sK5,X0,k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3466,c_3469])).

cnf(c_14020,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,X0),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_6607])).

cnf(c_29333,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3493,c_14020])).

cnf(c_11,plain,
    ( ~ v17_lattices(X0)
    | v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_9,plain,
    ( v13_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_733,plain,
    ( ~ v17_lattices(X0)
    | v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_9])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f162])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_733,c_43])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_2016,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_994,c_57])).

cnf(c_2017,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k3_lattices(sK5,k5_lattices(sK5),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_2016])).

cnf(c_2021,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_lattices(sK5,k5_lattices(sK5),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2017,c_59,c_58,c_56])).

cnf(c_3487,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_4874,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,X0)) = k7_lattices(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3487])).

cnf(c_9234,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(superposition,[status(thm)],[c_3493,c_4874])).

cnf(c_29341,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k5_lattices(sK5)) = k7_lattices(sK5,sK7) ),
    inference(light_normalisation,[status(thm)],[c_29333,c_9234])).

cnf(c_99456,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k7_lattices(sK5,k4_lattices(sK5,sK6,sK7))) = k7_lattices(sK5,sK7) ),
    inference(light_normalisation,[status(thm)],[c_99449,c_7625,c_19487,c_29341])).

cnf(c_48,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_2148,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_57])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2148])).

cnf(c_2153,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2149,c_59,c_58,c_56])).

cnf(c_3480,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2153])).

cnf(c_5957,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,X0)),k7_lattices(sK5,X0)) = k6_lattices(sK5)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3480])).

cnf(c_19546,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,k5_lattices(sK5))),k7_lattices(sK5,k5_lattices(sK5))) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3466,c_5957])).

cnf(c_4831,plain,
    ( k7_lattices(sK5,k7_lattices(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3466,c_3481])).

cnf(c_9237,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,k5_lattices(sK5))) = k7_lattices(sK5,k5_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_3466,c_4874])).

cnf(c_19548,plain,
    ( k7_lattices(sK5,k5_lattices(sK5)) = k6_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_19546,c_4831,c_9237])).

cnf(c_26,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_879,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_28,c_26])).

cnf(c_2659,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_879,c_59])).

cnf(c_2660,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2659])).

cnf(c_136,plain,
    ( l2_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_142,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l2_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2662,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2660,c_59,c_56,c_136,c_142])).

cnf(c_3465,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2662])).

cnf(c_82015,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,k6_lattices(sK5))) ),
    inference(superposition,[status(thm)],[c_3465,c_81292])).

cnf(c_7227,plain,
    ( k4_lattices(sK5,X0,sK6) = k4_lattices(sK5,sK6,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3470])).

cnf(c_7276,plain,
    ( k4_lattices(sK5,sK6,k6_lattices(sK5)) = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(superposition,[status(thm)],[c_3465,c_7227])).

cnf(c_8,plain,
    ( ~ v15_lattices(X0)
    | v14_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_750,plain,
    ( ~ v17_lattices(X0)
    | v14_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f164])).

cnf(c_931,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_750,c_45])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_2052,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k6_lattices(X1),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_932,c_57])).

cnf(c_2053,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,k6_lattices(sK5),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_2052])).

cnf(c_2057,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,k6_lattices(sK5),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_59,c_58,c_56])).

cnf(c_3485,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2057])).

cnf(c_4840,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_3492,c_3485])).

cnf(c_7280,plain,
    ( k4_lattices(sK5,sK6,k6_lattices(sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_7276,c_4840])).

cnf(c_6606,plain,
    ( k3_lattices(sK5,X0,k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3465,c_3469])).

cnf(c_13701,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,X0),k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_6606])).

cnf(c_29121,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3493,c_13701])).

cnf(c_46,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f165])).

cnf(c_907,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | X1 != X2
    | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1) ),
    inference(resolution_lifted,[status(thm)],[c_750,c_46])).

cnf(c_908,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_2070,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_908,c_57])).

cnf(c_2071,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k3_lattices(sK5,k6_lattices(sK5),X0) = k6_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2070])).

cnf(c_2075,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k3_lattices(sK5,k6_lattices(sK5),X0) = k6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2071,c_59,c_58,c_56])).

cnf(c_3484,plain,
    ( k3_lattices(sK5,k6_lattices(sK5),X0) = k6_lattices(sK5)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_5733,plain,
    ( k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,X0)) = k6_lattices(sK5)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3484])).

cnf(c_8792,plain,
    ( k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,sK7)) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3493,c_5733])).

cnf(c_29129,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5)) = k6_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_29121,c_8792])).

cnf(c_82019,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k6_lattices(sK5)) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_82015,c_7280,c_20310,c_29129])).

cnf(c_33,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_53,negated_conjecture,
    ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f177])).

cnf(c_450,plain,
    ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(prop_impl,[status(thm)],[c_53])).

cnf(c_1204,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k7_lattices(sK5,sK7) != X2
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_450])).

cnf(c_1205,plain,
    ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ v6_lattices(sK5)
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v9_lattices(sK5)
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1204])).

cnf(c_202,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_208,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_211,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | v9_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1207,plain,
    ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1205,c_59,c_58,c_56,c_55,c_202,c_208,c_211])).

cnf(c_3490,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_65,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_1209,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_3584,plain,
    ( m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2706])).

cnf(c_3585,plain,
    ( m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3584])).

cnf(c_8103,plain,
    ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3490,c_65,c_1209,c_3585])).

cnf(c_8104,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8103])).

cnf(c_37,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_1598,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(resolution,[status(thm)],[c_2,c_37])).

cnf(c_1602,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_lattices(X0,X1,X2)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_37,c_2,c_1])).

cnf(c_1603,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_1602])).

cnf(c_2247,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1603,c_58])).

cnf(c_2248,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_2247])).

cnf(c_2252,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2248,c_59,c_56])).

cnf(c_2253,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_2252])).

cnf(c_3477,plain,
    ( k2_lattices(sK5,X0,X1) = X0
    | r1_lattices(sK5,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2253])).

cnf(c_8107,plain,
    ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8104,c_3477])).

cnf(c_8108,plain,
    ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8107])).

cnf(c_93218,plain,
    ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8107,c_55,c_54,c_3584,c_8108])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_1311,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_1311])).

cnf(c_1485,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1312])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_1485])).

cnf(c_2397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1486,c_58])).

cnf(c_2398,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_2397])).

cnf(c_2402,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_59,c_56])).

cnf(c_3471,plain,
    ( k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2402])).

cnf(c_7291,plain,
    ( k2_lattices(sK5,sK6,X0) = k4_lattices(sK5,sK6,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3471])).

cnf(c_7354,plain,
    ( k2_lattices(sK5,sK6,k7_lattices(sK5,X0)) = k4_lattices(sK5,sK6,k7_lattices(sK5,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_7291])).

cnf(c_20913,plain,
    ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3493,c_7354])).

cnf(c_93220,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
    | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(demodulation,[status(thm)],[c_93218,c_20913])).

cnf(c_81269,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),X0),k3_lattices(sK5,k7_lattices(sK5,sK6),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_7823])).

cnf(c_81519,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,X0)),k3_lattices(sK5,k7_lattices(sK5,sK6),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,X0),X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_81269])).

cnf(c_88619,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,sK7),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_81519])).

cnf(c_7598,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,X0)) = k7_lattices(sK5,k4_lattices(sK5,sK6,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3482])).

cnf(c_7635,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,sK7)) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_3493,c_7598])).

cnf(c_88628,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,sK7),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_88619,c_7635])).

cnf(c_88696,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK6),sK6)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,sK7),sK6)) ),
    inference(superposition,[status(thm)],[c_3492,c_88628])).

cnf(c_5954,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3492,c_3480])).

cnf(c_7278,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,X0)) = k4_lattices(sK5,k7_lattices(sK5,X0),sK6)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_7227])).

cnf(c_20395,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3493,c_7278])).

cnf(c_81289,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)),k3_lattices(sK5,k7_lattices(sK5,sK7),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,X0),X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_81268])).

cnf(c_86831,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6)),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,sK6),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_81289])).

cnf(c_86838,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,sK6),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_86831,c_7625])).

cnf(c_87318,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5))) ),
    inference(superposition,[status(thm)],[c_3465,c_86838])).

cnf(c_7294,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,X0),X1) = k4_lattices(sK5,k7_lattices(sK5,X0),X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3471])).

cnf(c_23842,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),X0) = k4_lattices(sK5,k7_lattices(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_7294])).

cnf(c_23872,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) = k4_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_3465,c_23842])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_778,c_28])).

cnf(c_2460,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_796,c_58])).

cnf(c_2461,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_2460])).

cnf(c_2465,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2461,c_59,c_56])).

cnf(c_3468,plain,
    ( k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2465])).

cnf(c_6587,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,X0),X1) = k3_lattices(sK5,k7_lattices(sK5,X0),X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3468])).

cnf(c_21276,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK6),X0) = k3_lattices(sK5,k7_lattices(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_6587])).

cnf(c_21351,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_3492,c_21276])).

cnf(c_21355,plain,
    ( k1_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k6_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_21351,c_5954])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_59])).

cnf(c_2719,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | ~ v9_lattices(sK5)
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_2718])).

cnf(c_2350,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_58])).

cnf(c_2351,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | v9_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_2350])).

cnf(c_2353,plain,
    ( v9_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2351,c_59,c_58,c_56,c_211])).

cnf(c_2598,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2353])).

cnf(c_2599,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_2598])).

cnf(c_2723,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2719,c_59,c_56,c_2599])).

cnf(c_3467,plain,
    ( k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2723])).

cnf(c_5864,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,X0),k1_lattices(sK5,k7_lattices(sK5,X0),X1)) = k7_lattices(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3467])).

cnf(c_20515,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),k1_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k7_lattices(sK5,sK6)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_5864])).

cnf(c_20604,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),k1_lattices(sK5,k7_lattices(sK5,sK6),sK6)) = k7_lattices(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_3492,c_20515])).

cnf(c_21383,plain,
    ( k2_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) = k7_lattices(sK5,sK6) ),
    inference(demodulation,[status(thm)],[c_21355,c_20604])).

cnf(c_23875,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) = k7_lattices(sK5,sK6) ),
    inference(light_normalisation,[status(thm)],[c_23872,c_21383])).

cnf(c_87322,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k6_lattices(sK5)) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_87318,c_7625,c_23875,c_29129])).

cnf(c_88702,plain,
    ( k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_88696,c_5954,c_20395,c_87322])).

cnf(c_93224,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) = k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_93220,c_88702])).

cnf(c_93244,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) = k6_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_93224,c_5954])).

cnf(c_51,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_2088,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_57])).

cnf(c_2089,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_2088])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2089,c_59,c_58,c_56])).

cnf(c_2094,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1)) ),
    inference(renaming,[status(thm)],[c_2093])).

cnf(c_3483,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_7658,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,X0)),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,X0),X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3483])).

cnf(c_67663,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,sK6)),k7_lattices(sK5,X0)) = k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_7658])).

cnf(c_67669,plain,
    ( k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k4_lattices(sK5,sK6,k7_lattices(sK5,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67663,c_4829])).

cnf(c_67685,plain,
    ( k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,X0))) = k4_lattices(sK5,sK6,k7_lattices(sK5,k7_lattices(sK5,X0)))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_67669])).

cnf(c_67943,plain,
    ( k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,sK7))) = k4_lattices(sK5,sK6,k7_lattices(sK5,k7_lattices(sK5,sK7))) ),
    inference(superposition,[status(thm)],[c_3493,c_67685])).

cnf(c_4828,plain,
    ( k7_lattices(sK5,k7_lattices(sK5,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_3493,c_3481])).

cnf(c_67951,plain,
    ( k7_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7))) = k4_lattices(sK5,sK6,sK7) ),
    inference(light_normalisation,[status(thm)],[c_67943,c_4828,c_7635])).

cnf(c_93270,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
    | k7_lattices(sK5,k6_lattices(sK5)) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_93244,c_67951])).

cnf(c_19482,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,k6_lattices(sK5))),k7_lattices(sK5,k6_lattices(sK5))) = k5_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3465,c_5855])).

cnf(c_4830,plain,
    ( k7_lattices(sK5,k7_lattices(sK5,k6_lattices(sK5))) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3465,c_3481])).

cnf(c_4843,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,X0)) = k7_lattices(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3485])).

cnf(c_8803,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,k6_lattices(sK5))) = k7_lattices(sK5,k6_lattices(sK5)) ),
    inference(superposition,[status(thm)],[c_3465,c_4843])).

cnf(c_19486,plain,
    ( k7_lattices(sK5,k6_lattices(sK5)) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_19482,c_4830,c_8803])).

cnf(c_93273,plain,
    ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_93270,c_19486])).

cnf(c_99457,plain,
    ( k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
    inference(demodulation,[status(thm)],[c_99456,c_19548,c_82019,c_93273])).

cnf(c_7820,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,X0),k3_lattices(sK5,sK6,X1)) = k3_lattices(sK5,sK6,k4_lattices(sK5,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3489])).

cnf(c_7871,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,X0)),k3_lattices(sK5,sK6,X1)) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,X0),X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_7820])).

cnf(c_82969,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,X0)) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_7871])).

cnf(c_82991,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,k7_lattices(sK5,X0))) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_82969])).

cnf(c_84257,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,k7_lattices(sK5,k6_lattices(sK5)))) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,k6_lattices(sK5)))) ),
    inference(superposition,[status(thm)],[c_3465,c_82991])).

cnf(c_7212,plain,
    ( k3_lattices(sK5,sK6,k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),sK6) ),
    inference(superposition,[status(thm)],[c_3466,c_6605])).

cnf(c_4871,plain,
    ( k3_lattices(sK5,k5_lattices(sK5),sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_3492,c_3487])).

cnf(c_7214,plain,
    ( k3_lattices(sK5,sK6,k5_lattices(sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_7212,c_4871])).

cnf(c_7654,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)) = k7_lattices(sK5,k3_lattices(sK5,sK7,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_3483])).

cnf(c_7677,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,k6_lattices(sK5))) = k7_lattices(sK5,k3_lattices(sK5,sK7,k6_lattices(sK5))) ),
    inference(superposition,[status(thm)],[c_3465,c_7654])).

cnf(c_6604,plain,
    ( k3_lattices(sK5,X0,sK7) = k3_lattices(sK5,sK7,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_3469])).

cnf(c_7139,plain,
    ( k3_lattices(sK5,sK7,k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),sK7) ),
    inference(superposition,[status(thm)],[c_3465,c_6604])).

cnf(c_5729,plain,
    ( k3_lattices(sK5,k6_lattices(sK5),sK7) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_3493,c_3484])).

cnf(c_7143,plain,
    ( k3_lattices(sK5,sK7,k6_lattices(sK5)) = k6_lattices(sK5) ),
    inference(light_normalisation,[status(thm)],[c_7139,c_5729])).

cnf(c_7681,plain,
    ( k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,k6_lattices(sK5))) = k7_lattices(sK5,k6_lattices(sK5)) ),
    inference(light_normalisation,[status(thm)],[c_7677,c_7143])).

cnf(c_82988,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,sK6)) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),sK6)) ),
    inference(superposition,[status(thm)],[c_3492,c_82969])).

cnf(c_6584,plain,
    ( k1_lattices(sK5,sK6,X0) = k3_lattices(sK5,sK6,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_3468])).

cnf(c_6979,plain,
    ( k1_lattices(sK5,sK6,sK6) = k3_lattices(sK5,sK6,sK6) ),
    inference(superposition,[status(thm)],[c_3492,c_6584])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f153])).

cnf(c_1537,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v9_lattices(X1)
    | X1 != X2
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_34])).

cnf(c_1538,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1537])).

cnf(c_1556,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1538,c_1,c_2])).

cnf(c_2361,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1556,c_58])).

cnf(c_2362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_2361])).

cnf(c_2366,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k1_lattices(sK5,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_59,c_56])).

cnf(c_3473,plain,
    ( k1_lattices(sK5,X0,X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_4076,plain,
    ( k1_lattices(sK5,sK6,sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_3492,c_3473])).

cnf(c_6983,plain,
    ( k3_lattices(sK5,sK6,sK6) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_6979,c_4076])).

cnf(c_82994,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),sK6) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) ),
    inference(light_normalisation,[status(thm)],[c_82988,c_6983,c_20395])).

cnf(c_84261,plain,
    ( k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k3_lattices(sK5,sK6,k7_lattices(sK5,k6_lattices(sK5))) ),
    inference(light_normalisation,[status(thm)],[c_84257,c_7214,c_7681,c_19486,c_82994])).

cnf(c_84262,plain,
    ( k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = sK6 ),
    inference(demodulation,[status(thm)],[c_84261,c_7214,c_19486])).

cnf(c_7868,plain,
    ( k4_lattices(sK5,k3_lattices(sK5,sK6,sK6),k3_lattices(sK5,sK6,X0)) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_7820])).

cnf(c_7874,plain,
    ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,X0)) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7868,c_6983])).

cnf(c_23709,plain,
    ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,k7_lattices(sK5,X0))) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,X0)))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_7874])).

cnf(c_37071,plain,
    ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) ),
    inference(superposition,[status(thm)],[c_3493,c_23709])).

cnf(c_99160,plain,
    ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = sK6 ),
    inference(demodulation,[status(thm)],[c_84262,c_37071])).

cnf(c_99655,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6 ),
    inference(demodulation,[status(thm)],[c_99457,c_99160])).

cnf(c_36,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_1630,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(resolution,[status(thm)],[c_2,c_36])).

cnf(c_1634,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_36,c_2,c_1])).

cnf(c_1635,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(renaming,[status(thm)],[c_1634])).

cnf(c_2223,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1635,c_58])).

cnf(c_2224,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_2223])).

cnf(c_2228,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2224,c_59,c_56])).

cnf(c_2229,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_2228])).

cnf(c_3478,plain,
    ( k2_lattices(sK5,X0,X1) != X0
    | r1_lattices(sK5,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2229])).

cnf(c_20925,plain,
    ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != sK6
    | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
    | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20913,c_3478])).

cnf(c_20926,plain,
    ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20925])).

cnf(c_32,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_52,negated_conjecture,
    ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_448,plain,
    ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(prop_impl,[status(thm)],[c_52])).

cnf(c_1187,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)
    | k7_lattices(sK5,sK7) != X2
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_448])).

cnf(c_1188,plain,
    ( ~ r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ v6_lattices(sK5)
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v9_lattices(sK5)
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_1187])).

cnf(c_1190,plain,
    ( ~ r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
    | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
    | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1188,c_59,c_58,c_56,c_55,c_202,c_208,c_211])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99655,c_93273,c_20926,c_3584,c_1190,c_54,c_55])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.57/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.57/3.49  
% 23.57/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.57/3.49  
% 23.57/3.49  ------  iProver source info
% 23.57/3.49  
% 23.57/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.57/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.57/3.49  git: non_committed_changes: false
% 23.57/3.49  git: last_make_outside_of_git: false
% 23.57/3.49  
% 23.57/3.49  ------ 
% 23.57/3.49  
% 23.57/3.49  ------ Input Options
% 23.57/3.49  
% 23.57/3.49  --out_options                           all
% 23.57/3.49  --tptp_safe_out                         true
% 23.57/3.49  --problem_path                          ""
% 23.57/3.49  --include_path                          ""
% 23.57/3.49  --clausifier                            res/vclausify_rel
% 23.57/3.49  --clausifier_options                    ""
% 23.57/3.49  --stdin                                 false
% 23.57/3.49  --stats_out                             all
% 23.57/3.49  
% 23.57/3.49  ------ General Options
% 23.57/3.49  
% 23.57/3.49  --fof                                   false
% 23.57/3.49  --time_out_real                         305.
% 23.57/3.49  --time_out_virtual                      -1.
% 23.57/3.49  --symbol_type_check                     false
% 23.57/3.49  --clausify_out                          false
% 23.57/3.49  --sig_cnt_out                           false
% 23.57/3.49  --trig_cnt_out                          false
% 23.57/3.49  --trig_cnt_out_tolerance                1.
% 23.57/3.49  --trig_cnt_out_sk_spl                   false
% 23.57/3.49  --abstr_cl_out                          false
% 23.57/3.49  
% 23.57/3.49  ------ Global Options
% 23.57/3.49  
% 23.57/3.49  --schedule                              default
% 23.57/3.49  --add_important_lit                     false
% 23.57/3.49  --prop_solver_per_cl                    1000
% 23.57/3.49  --min_unsat_core                        false
% 23.57/3.49  --soft_assumptions                      false
% 23.57/3.49  --soft_lemma_size                       3
% 23.57/3.49  --prop_impl_unit_size                   0
% 23.57/3.49  --prop_impl_unit                        []
% 23.57/3.49  --share_sel_clauses                     true
% 23.57/3.49  --reset_solvers                         false
% 23.57/3.49  --bc_imp_inh                            [conj_cone]
% 23.57/3.49  --conj_cone_tolerance                   3.
% 23.57/3.49  --extra_neg_conj                        none
% 23.57/3.49  --large_theory_mode                     true
% 23.57/3.49  --prolific_symb_bound                   200
% 23.57/3.49  --lt_threshold                          2000
% 23.57/3.49  --clause_weak_htbl                      true
% 23.57/3.49  --gc_record_bc_elim                     false
% 23.57/3.49  
% 23.57/3.49  ------ Preprocessing Options
% 23.57/3.49  
% 23.57/3.49  --preprocessing_flag                    true
% 23.57/3.49  --time_out_prep_mult                    0.1
% 23.57/3.49  --splitting_mode                        input
% 23.57/3.49  --splitting_grd                         true
% 23.57/3.49  --splitting_cvd                         false
% 23.57/3.49  --splitting_cvd_svl                     false
% 23.57/3.49  --splitting_nvd                         32
% 23.57/3.49  --sub_typing                            true
% 23.57/3.49  --prep_gs_sim                           true
% 23.57/3.49  --prep_unflatten                        true
% 23.57/3.49  --prep_res_sim                          true
% 23.57/3.49  --prep_upred                            true
% 23.57/3.49  --prep_sem_filter                       exhaustive
% 23.57/3.49  --prep_sem_filter_out                   false
% 23.57/3.49  --pred_elim                             true
% 23.57/3.49  --res_sim_input                         true
% 23.57/3.49  --eq_ax_congr_red                       true
% 23.57/3.49  --pure_diseq_elim                       true
% 23.57/3.49  --brand_transform                       false
% 23.57/3.49  --non_eq_to_eq                          false
% 23.57/3.49  --prep_def_merge                        true
% 23.57/3.49  --prep_def_merge_prop_impl              false
% 23.57/3.49  --prep_def_merge_mbd                    true
% 23.57/3.49  --prep_def_merge_tr_red                 false
% 23.57/3.49  --prep_def_merge_tr_cl                  false
% 23.57/3.49  --smt_preprocessing                     true
% 23.57/3.49  --smt_ac_axioms                         fast
% 23.57/3.49  --preprocessed_out                      false
% 23.57/3.49  --preprocessed_stats                    false
% 23.57/3.49  
% 23.57/3.49  ------ Abstraction refinement Options
% 23.57/3.49  
% 23.57/3.49  --abstr_ref                             []
% 23.57/3.49  --abstr_ref_prep                        false
% 23.57/3.49  --abstr_ref_until_sat                   false
% 23.57/3.49  --abstr_ref_sig_restrict                funpre
% 23.57/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.57/3.49  --abstr_ref_under                       []
% 23.57/3.49  
% 23.57/3.49  ------ SAT Options
% 23.57/3.49  
% 23.57/3.49  --sat_mode                              false
% 23.57/3.49  --sat_fm_restart_options                ""
% 23.57/3.49  --sat_gr_def                            false
% 23.57/3.49  --sat_epr_types                         true
% 23.57/3.49  --sat_non_cyclic_types                  false
% 23.57/3.49  --sat_finite_models                     false
% 23.57/3.49  --sat_fm_lemmas                         false
% 23.57/3.49  --sat_fm_prep                           false
% 23.57/3.49  --sat_fm_uc_incr                        true
% 23.57/3.49  --sat_out_model                         small
% 23.57/3.49  --sat_out_clauses                       false
% 23.57/3.49  
% 23.57/3.49  ------ QBF Options
% 23.57/3.49  
% 23.57/3.49  --qbf_mode                              false
% 23.57/3.49  --qbf_elim_univ                         false
% 23.57/3.49  --qbf_dom_inst                          none
% 23.57/3.49  --qbf_dom_pre_inst                      false
% 23.57/3.49  --qbf_sk_in                             false
% 23.57/3.49  --qbf_pred_elim                         true
% 23.57/3.49  --qbf_split                             512
% 23.57/3.49  
% 23.57/3.49  ------ BMC1 Options
% 23.57/3.49  
% 23.57/3.49  --bmc1_incremental                      false
% 23.57/3.49  --bmc1_axioms                           reachable_all
% 23.57/3.49  --bmc1_min_bound                        0
% 23.57/3.49  --bmc1_max_bound                        -1
% 23.57/3.49  --bmc1_max_bound_default                -1
% 23.57/3.49  --bmc1_symbol_reachability              true
% 23.57/3.49  --bmc1_property_lemmas                  false
% 23.57/3.49  --bmc1_k_induction                      false
% 23.57/3.49  --bmc1_non_equiv_states                 false
% 23.57/3.49  --bmc1_deadlock                         false
% 23.57/3.49  --bmc1_ucm                              false
% 23.57/3.49  --bmc1_add_unsat_core                   none
% 23.57/3.49  --bmc1_unsat_core_children              false
% 23.57/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.57/3.49  --bmc1_out_stat                         full
% 23.57/3.49  --bmc1_ground_init                      false
% 23.57/3.49  --bmc1_pre_inst_next_state              false
% 23.57/3.49  --bmc1_pre_inst_state                   false
% 23.57/3.49  --bmc1_pre_inst_reach_state             false
% 23.57/3.49  --bmc1_out_unsat_core                   false
% 23.57/3.49  --bmc1_aig_witness_out                  false
% 23.57/3.49  --bmc1_verbose                          false
% 23.57/3.49  --bmc1_dump_clauses_tptp                false
% 23.57/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.57/3.49  --bmc1_dump_file                        -
% 23.57/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.57/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.57/3.49  --bmc1_ucm_extend_mode                  1
% 23.57/3.49  --bmc1_ucm_init_mode                    2
% 23.57/3.49  --bmc1_ucm_cone_mode                    none
% 23.57/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.57/3.49  --bmc1_ucm_relax_model                  4
% 23.57/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.57/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.57/3.49  --bmc1_ucm_layered_model                none
% 23.57/3.49  --bmc1_ucm_max_lemma_size               10
% 23.57/3.49  
% 23.57/3.49  ------ AIG Options
% 23.57/3.49  
% 23.57/3.49  --aig_mode                              false
% 23.57/3.49  
% 23.57/3.49  ------ Instantiation Options
% 23.57/3.49  
% 23.57/3.49  --instantiation_flag                    true
% 23.57/3.49  --inst_sos_flag                         true
% 23.57/3.49  --inst_sos_phase                        true
% 23.57/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.57/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.57/3.49  --inst_lit_sel_side                     num_symb
% 23.57/3.49  --inst_solver_per_active                1400
% 23.57/3.49  --inst_solver_calls_frac                1.
% 23.57/3.49  --inst_passive_queue_type               priority_queues
% 23.57/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.57/3.49  --inst_passive_queues_freq              [25;2]
% 23.57/3.49  --inst_dismatching                      true
% 23.57/3.49  --inst_eager_unprocessed_to_passive     true
% 23.57/3.49  --inst_prop_sim_given                   true
% 23.57/3.49  --inst_prop_sim_new                     false
% 23.57/3.49  --inst_subs_new                         false
% 23.57/3.49  --inst_eq_res_simp                      false
% 23.57/3.49  --inst_subs_given                       false
% 23.57/3.49  --inst_orphan_elimination               true
% 23.57/3.49  --inst_learning_loop_flag               true
% 23.57/3.49  --inst_learning_start                   3000
% 23.57/3.49  --inst_learning_factor                  2
% 23.57/3.49  --inst_start_prop_sim_after_learn       3
% 23.57/3.49  --inst_sel_renew                        solver
% 23.57/3.49  --inst_lit_activity_flag                true
% 23.57/3.49  --inst_restr_to_given                   false
% 23.57/3.49  --inst_activity_threshold               500
% 23.57/3.49  --inst_out_proof                        true
% 23.57/3.49  
% 23.57/3.49  ------ Resolution Options
% 23.57/3.49  
% 23.57/3.49  --resolution_flag                       true
% 23.57/3.49  --res_lit_sel                           adaptive
% 23.57/3.49  --res_lit_sel_side                      none
% 23.57/3.49  --res_ordering                          kbo
% 23.57/3.49  --res_to_prop_solver                    active
% 23.57/3.49  --res_prop_simpl_new                    false
% 23.57/3.49  --res_prop_simpl_given                  true
% 23.57/3.49  --res_passive_queue_type                priority_queues
% 23.57/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.57/3.49  --res_passive_queues_freq               [15;5]
% 23.57/3.49  --res_forward_subs                      full
% 23.57/3.49  --res_backward_subs                     full
% 23.57/3.49  --res_forward_subs_resolution           true
% 23.57/3.49  --res_backward_subs_resolution          true
% 23.57/3.49  --res_orphan_elimination                true
% 23.57/3.49  --res_time_limit                        2.
% 23.57/3.49  --res_out_proof                         true
% 23.57/3.49  
% 23.57/3.49  ------ Superposition Options
% 23.57/3.49  
% 23.57/3.49  --superposition_flag                    true
% 23.57/3.49  --sup_passive_queue_type                priority_queues
% 23.57/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.57/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.57/3.49  --demod_completeness_check              fast
% 23.57/3.49  --demod_use_ground                      true
% 23.57/3.49  --sup_to_prop_solver                    passive
% 23.57/3.49  --sup_prop_simpl_new                    true
% 23.57/3.49  --sup_prop_simpl_given                  true
% 23.57/3.49  --sup_fun_splitting                     true
% 23.57/3.49  --sup_smt_interval                      50000
% 23.57/3.49  
% 23.57/3.49  ------ Superposition Simplification Setup
% 23.57/3.49  
% 23.57/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.57/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.57/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.57/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.57/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.57/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.57/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.57/3.49  --sup_immed_triv                        [TrivRules]
% 23.57/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.57/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.57/3.49  --sup_immed_bw_main                     []
% 23.57/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.57/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.57/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.57/3.49  --sup_input_bw                          []
% 23.57/3.49  
% 23.57/3.49  ------ Combination Options
% 23.57/3.49  
% 23.57/3.49  --comb_res_mult                         3
% 23.57/3.49  --comb_sup_mult                         2
% 23.57/3.49  --comb_inst_mult                        10
% 23.57/3.49  
% 23.57/3.49  ------ Debug Options
% 23.57/3.49  
% 23.57/3.49  --dbg_backtrace                         false
% 23.57/3.49  --dbg_dump_prop_clauses                 false
% 23.57/3.49  --dbg_dump_prop_clauses_file            -
% 23.57/3.49  --dbg_out_stat                          false
% 23.57/3.49  ------ Parsing...
% 23.57/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.57/3.49  
% 23.57/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 23.57/3.49  
% 23.57/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.57/3.49  
% 23.57/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.57/3.49  ------ Proving...
% 23.57/3.49  ------ Problem Properties 
% 23.57/3.49  
% 23.57/3.49  
% 23.57/3.49  clauses                                 32
% 23.57/3.49  conjectures                             2
% 23.57/3.49  EPR                                     0
% 23.57/3.49  Horn                                    31
% 23.57/3.49  unary                                   4
% 23.57/3.49  binary                                  11
% 23.57/3.49  lits                                    85
% 23.57/3.49  lits eq                                 25
% 23.57/3.49  fd_pure                                 0
% 23.57/3.49  fd_pseudo                               0
% 23.57/3.49  fd_cond                                 0
% 23.57/3.49  fd_pseudo_cond                          1
% 23.57/3.49  AC symbols                              0
% 23.57/3.49  
% 23.57/3.49  ------ Schedule dynamic 5 is on 
% 23.57/3.49  
% 23.57/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.57/3.49  
% 23.57/3.49  
% 23.57/3.49  ------ 
% 23.57/3.49  Current options:
% 23.57/3.49  ------ 
% 23.57/3.49  
% 23.57/3.49  ------ Input Options
% 23.57/3.49  
% 23.57/3.49  --out_options                           all
% 23.57/3.49  --tptp_safe_out                         true
% 23.57/3.49  --problem_path                          ""
% 23.57/3.49  --include_path                          ""
% 23.57/3.49  --clausifier                            res/vclausify_rel
% 23.57/3.49  --clausifier_options                    ""
% 23.57/3.49  --stdin                                 false
% 23.57/3.49  --stats_out                             all
% 23.57/3.49  
% 23.57/3.49  ------ General Options
% 23.57/3.49  
% 23.57/3.49  --fof                                   false
% 23.57/3.49  --time_out_real                         305.
% 23.57/3.49  --time_out_virtual                      -1.
% 23.57/3.49  --symbol_type_check                     false
% 23.57/3.49  --clausify_out                          false
% 23.57/3.49  --sig_cnt_out                           false
% 23.57/3.49  --trig_cnt_out                          false
% 23.57/3.49  --trig_cnt_out_tolerance                1.
% 23.57/3.49  --trig_cnt_out_sk_spl                   false
% 23.57/3.49  --abstr_cl_out                          false
% 23.57/3.49  
% 23.57/3.49  ------ Global Options
% 23.57/3.49  
% 23.57/3.49  --schedule                              default
% 23.57/3.49  --add_important_lit                     false
% 23.57/3.49  --prop_solver_per_cl                    1000
% 23.57/3.49  --min_unsat_core                        false
% 23.57/3.49  --soft_assumptions                      false
% 23.57/3.49  --soft_lemma_size                       3
% 23.57/3.49  --prop_impl_unit_size                   0
% 23.57/3.49  --prop_impl_unit                        []
% 23.57/3.49  --share_sel_clauses                     true
% 23.57/3.49  --reset_solvers                         false
% 23.57/3.49  --bc_imp_inh                            [conj_cone]
% 23.57/3.49  --conj_cone_tolerance                   3.
% 23.57/3.49  --extra_neg_conj                        none
% 23.57/3.49  --large_theory_mode                     true
% 23.57/3.49  --prolific_symb_bound                   200
% 23.57/3.49  --lt_threshold                          2000
% 23.57/3.49  --clause_weak_htbl                      true
% 23.57/3.49  --gc_record_bc_elim                     false
% 23.57/3.49  
% 23.57/3.49  ------ Preprocessing Options
% 23.57/3.49  
% 23.57/3.49  --preprocessing_flag                    true
% 23.57/3.49  --time_out_prep_mult                    0.1
% 23.57/3.49  --splitting_mode                        input
% 23.57/3.49  --splitting_grd                         true
% 23.57/3.49  --splitting_cvd                         false
% 23.57/3.49  --splitting_cvd_svl                     false
% 23.57/3.49  --splitting_nvd                         32
% 23.57/3.49  --sub_typing                            true
% 23.57/3.49  --prep_gs_sim                           true
% 23.57/3.49  --prep_unflatten                        true
% 23.57/3.49  --prep_res_sim                          true
% 23.57/3.49  --prep_upred                            true
% 23.57/3.49  --prep_sem_filter                       exhaustive
% 23.57/3.49  --prep_sem_filter_out                   false
% 23.57/3.49  --pred_elim                             true
% 23.57/3.49  --res_sim_input                         true
% 23.57/3.49  --eq_ax_congr_red                       true
% 23.57/3.49  --pure_diseq_elim                       true
% 23.57/3.49  --brand_transform                       false
% 23.57/3.49  --non_eq_to_eq                          false
% 23.57/3.49  --prep_def_merge                        true
% 23.57/3.49  --prep_def_merge_prop_impl              false
% 23.57/3.49  --prep_def_merge_mbd                    true
% 23.57/3.49  --prep_def_merge_tr_red                 false
% 23.57/3.49  --prep_def_merge_tr_cl                  false
% 23.57/3.49  --smt_preprocessing                     true
% 23.57/3.49  --smt_ac_axioms                         fast
% 23.57/3.49  --preprocessed_out                      false
% 23.57/3.49  --preprocessed_stats                    false
% 23.57/3.49  
% 23.57/3.49  ------ Abstraction refinement Options
% 23.57/3.49  
% 23.57/3.49  --abstr_ref                             []
% 23.57/3.49  --abstr_ref_prep                        false
% 23.57/3.49  --abstr_ref_until_sat                   false
% 23.57/3.49  --abstr_ref_sig_restrict                funpre
% 23.57/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.57/3.49  --abstr_ref_under                       []
% 23.57/3.49  
% 23.57/3.49  ------ SAT Options
% 23.57/3.49  
% 23.57/3.49  --sat_mode                              false
% 23.57/3.49  --sat_fm_restart_options                ""
% 23.57/3.49  --sat_gr_def                            false
% 23.57/3.49  --sat_epr_types                         true
% 23.57/3.49  --sat_non_cyclic_types                  false
% 23.57/3.49  --sat_finite_models                     false
% 23.57/3.49  --sat_fm_lemmas                         false
% 23.57/3.49  --sat_fm_prep                           false
% 23.57/3.49  --sat_fm_uc_incr                        true
% 23.57/3.49  --sat_out_model                         small
% 23.57/3.49  --sat_out_clauses                       false
% 23.57/3.49  
% 23.57/3.49  ------ QBF Options
% 23.57/3.49  
% 23.57/3.49  --qbf_mode                              false
% 23.57/3.49  --qbf_elim_univ                         false
% 23.57/3.49  --qbf_dom_inst                          none
% 23.57/3.49  --qbf_dom_pre_inst                      false
% 23.57/3.49  --qbf_sk_in                             false
% 23.57/3.49  --qbf_pred_elim                         true
% 23.57/3.49  --qbf_split                             512
% 23.57/3.49  
% 23.57/3.49  ------ BMC1 Options
% 23.57/3.49  
% 23.57/3.49  --bmc1_incremental                      false
% 23.57/3.49  --bmc1_axioms                           reachable_all
% 23.57/3.49  --bmc1_min_bound                        0
% 23.57/3.49  --bmc1_max_bound                        -1
% 23.57/3.49  --bmc1_max_bound_default                -1
% 23.57/3.49  --bmc1_symbol_reachability              true
% 23.57/3.49  --bmc1_property_lemmas                  false
% 23.57/3.49  --bmc1_k_induction                      false
% 23.57/3.49  --bmc1_non_equiv_states                 false
% 23.57/3.49  --bmc1_deadlock                         false
% 23.57/3.49  --bmc1_ucm                              false
% 23.57/3.49  --bmc1_add_unsat_core                   none
% 23.57/3.49  --bmc1_unsat_core_children              false
% 23.57/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.57/3.49  --bmc1_out_stat                         full
% 23.57/3.49  --bmc1_ground_init                      false
% 23.57/3.49  --bmc1_pre_inst_next_state              false
% 23.57/3.49  --bmc1_pre_inst_state                   false
% 23.57/3.49  --bmc1_pre_inst_reach_state             false
% 23.57/3.49  --bmc1_out_unsat_core                   false
% 23.57/3.49  --bmc1_aig_witness_out                  false
% 23.57/3.49  --bmc1_verbose                          false
% 23.57/3.49  --bmc1_dump_clauses_tptp                false
% 23.57/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.57/3.49  --bmc1_dump_file                        -
% 23.57/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.57/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.57/3.49  --bmc1_ucm_extend_mode                  1
% 23.57/3.49  --bmc1_ucm_init_mode                    2
% 23.57/3.49  --bmc1_ucm_cone_mode                    none
% 23.57/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.57/3.49  --bmc1_ucm_relax_model                  4
% 23.57/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.57/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.57/3.49  --bmc1_ucm_layered_model                none
% 23.57/3.49  --bmc1_ucm_max_lemma_size               10
% 23.57/3.49  
% 23.57/3.49  ------ AIG Options
% 23.57/3.49  
% 23.57/3.49  --aig_mode                              false
% 23.57/3.49  
% 23.57/3.49  ------ Instantiation Options
% 23.57/3.49  
% 23.57/3.49  --instantiation_flag                    true
% 23.57/3.49  --inst_sos_flag                         true
% 23.57/3.49  --inst_sos_phase                        true
% 23.57/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.57/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.57/3.49  --inst_lit_sel_side                     none
% 23.57/3.49  --inst_solver_per_active                1400
% 23.57/3.49  --inst_solver_calls_frac                1.
% 23.57/3.49  --inst_passive_queue_type               priority_queues
% 23.57/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.57/3.49  --inst_passive_queues_freq              [25;2]
% 23.57/3.49  --inst_dismatching                      true
% 23.57/3.49  --inst_eager_unprocessed_to_passive     true
% 23.57/3.49  --inst_prop_sim_given                   true
% 23.57/3.49  --inst_prop_sim_new                     false
% 23.57/3.49  --inst_subs_new                         false
% 23.57/3.49  --inst_eq_res_simp                      false
% 23.57/3.49  --inst_subs_given                       false
% 23.57/3.49  --inst_orphan_elimination               true
% 23.57/3.49  --inst_learning_loop_flag               true
% 23.57/3.49  --inst_learning_start                   3000
% 23.57/3.49  --inst_learning_factor                  2
% 23.57/3.49  --inst_start_prop_sim_after_learn       3
% 23.57/3.49  --inst_sel_renew                        solver
% 23.57/3.49  --inst_lit_activity_flag                true
% 23.57/3.49  --inst_restr_to_given                   false
% 23.57/3.49  --inst_activity_threshold               500
% 23.57/3.49  --inst_out_proof                        true
% 23.57/3.49  
% 23.57/3.49  ------ Resolution Options
% 23.57/3.49  
% 23.57/3.49  --resolution_flag                       false
% 23.57/3.49  --res_lit_sel                           adaptive
% 23.57/3.49  --res_lit_sel_side                      none
% 23.57/3.49  --res_ordering                          kbo
% 23.57/3.49  --res_to_prop_solver                    active
% 23.57/3.49  --res_prop_simpl_new                    false
% 23.57/3.49  --res_prop_simpl_given                  true
% 23.57/3.49  --res_passive_queue_type                priority_queues
% 23.57/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.57/3.49  --res_passive_queues_freq               [15;5]
% 23.57/3.49  --res_forward_subs                      full
% 23.57/3.49  --res_backward_subs                     full
% 23.57/3.49  --res_forward_subs_resolution           true
% 23.57/3.49  --res_backward_subs_resolution          true
% 23.57/3.49  --res_orphan_elimination                true
% 23.57/3.49  --res_time_limit                        2.
% 23.57/3.49  --res_out_proof                         true
% 23.57/3.49  
% 23.57/3.49  ------ Superposition Options
% 23.57/3.49  
% 23.57/3.49  --superposition_flag                    true
% 23.57/3.49  --sup_passive_queue_type                priority_queues
% 23.57/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.57/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.57/3.49  --demod_completeness_check              fast
% 23.57/3.49  --demod_use_ground                      true
% 23.57/3.49  --sup_to_prop_solver                    passive
% 23.57/3.49  --sup_prop_simpl_new                    true
% 23.57/3.49  --sup_prop_simpl_given                  true
% 23.57/3.49  --sup_fun_splitting                     true
% 23.57/3.49  --sup_smt_interval                      50000
% 23.57/3.49  
% 23.57/3.49  ------ Superposition Simplification Setup
% 23.57/3.49  
% 23.57/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.57/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.57/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.57/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.57/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.57/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.57/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.57/3.49  --sup_immed_triv                        [TrivRules]
% 23.57/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.57/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.57/3.49  --sup_immed_bw_main                     []
% 23.57/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.57/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.57/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.57/3.49  --sup_input_bw                          []
% 23.57/3.49  
% 23.57/3.49  ------ Combination Options
% 23.57/3.49  
% 23.57/3.49  --comb_res_mult                         3
% 23.57/3.49  --comb_sup_mult                         2
% 23.57/3.49  --comb_inst_mult                        10
% 23.57/3.49  
% 23.57/3.49  ------ Debug Options
% 23.57/3.49  
% 23.57/3.49  --dbg_backtrace                         false
% 23.57/3.49  --dbg_dump_prop_clauses                 false
% 23.57/3.49  --dbg_dump_prop_clauses_file            -
% 23.57/3.49  --dbg_out_stat                          false
% 23.57/3.49  
% 23.57/3.49  
% 23.57/3.49  
% 23.57/3.49  
% 23.57/3.49  ------ Proving...
% 23.57/3.49  
% 23.57/3.49  
% 23.57/3.49  % SZS status Theorem for theBenchmark.p
% 23.57/3.49  
% 23.57/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.57/3.49  
% 23.57/3.49  fof(f33,conjecture,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f34,negated_conjecture,(
% 23.57/3.49    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 23.57/3.49    inference(negated_conjecture,[],[f33])).
% 23.57/3.49  
% 23.57/3.49  fof(f98,plain,(
% 23.57/3.49    ? [X0] : (? [X1] : (? [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <~> r3_lattices(X0,X1,k7_lattices(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f34])).
% 23.57/3.49  
% 23.57/3.49  fof(f99,plain,(
% 23.57/3.49    ? [X0] : (? [X1] : (? [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <~> r3_lattices(X0,X1,k7_lattices(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f98])).
% 23.57/3.49  
% 23.57/3.49  fof(f113,plain,(
% 23.57/3.49    ? [X0] : (? [X1] : (? [X2] : (((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 23.57/3.49    inference(nnf_transformation,[],[f99])).
% 23.57/3.49  
% 23.57/3.49  fof(f114,plain,(
% 23.57/3.49    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f113])).
% 23.57/3.49  
% 23.57/3.49  fof(f117,plain,(
% 23.57/3.49    ( ! [X0,X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r3_lattices(X0,X1,k7_lattices(X0,sK7)) | k4_lattices(X0,X1,sK7) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,sK7)) | k4_lattices(X0,X1,sK7) = k5_lattices(X0)) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 23.57/3.49    introduced(choice_axiom,[])).
% 23.57/3.49  
% 23.57/3.49  fof(f116,plain,(
% 23.57/3.49    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_lattices(X0,sK6,k7_lattices(X0,X2)) | k4_lattices(X0,sK6,X2) != k5_lattices(X0)) & (r3_lattices(X0,sK6,k7_lattices(X0,X2)) | k4_lattices(X0,sK6,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 23.57/3.49    introduced(choice_axiom,[])).
% 23.57/3.49  
% 23.57/3.49  fof(f115,plain,(
% 23.57/3.49    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK5,X1,k7_lattices(sK5,X2)) | k4_lattices(sK5,X1,X2) != k5_lattices(sK5)) & (r3_lattices(sK5,X1,k7_lattices(sK5,X2)) | k4_lattices(sK5,X1,X2) = k5_lattices(sK5)) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_subset_1(X1,u1_struct_0(sK5))) & l3_lattices(sK5) & v17_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 23.57/3.49    introduced(choice_axiom,[])).
% 23.57/3.49  
% 23.57/3.49  fof(f118,plain,(
% 23.57/3.49    (((~r3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)) & (r3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l3_lattices(sK5) & v17_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 23.57/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f114,f117,f116,f115])).
% 23.57/3.49  
% 23.57/3.49  fof(f175,plain,(
% 23.57/3.49    m1_subset_1(sK6,u1_struct_0(sK5))),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f11,axiom,(
% 23.57/3.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f55,plain,(
% 23.57/3.49    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f11])).
% 23.57/3.49  
% 23.57/3.49  fof(f56,plain,(
% 23.57/3.49    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f55])).
% 23.57/3.49  
% 23.57/3.49  fof(f146,plain,(
% 23.57/3.49    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f56])).
% 23.57/3.49  
% 23.57/3.49  fof(f171,plain,(
% 23.57/3.49    ~v2_struct_0(sK5)),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f174,plain,(
% 23.57/3.49    l3_lattices(sK5)),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f176,plain,(
% 23.57/3.49    m1_subset_1(sK7,u1_struct_0(sK5))),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f4,axiom,(
% 23.57/3.49    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f35,plain,(
% 23.57/3.49    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 23.57/3.49    inference(pure_predicate_removal,[],[f4])).
% 23.57/3.49  
% 23.57/3.49  fof(f41,plain,(
% 23.57/3.49    ! [X0] : (((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 23.57/3.49    inference(ennf_transformation,[],[f35])).
% 23.57/3.49  
% 23.57/3.49  fof(f42,plain,(
% 23.57/3.49    ! [X0] : ((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 23.57/3.49    inference(flattening,[],[f41])).
% 23.57/3.49  
% 23.57/3.49  fof(f131,plain,(
% 23.57/3.49    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f42])).
% 23.57/3.49  
% 23.57/3.49  fof(f22,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f76,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f22])).
% 23.57/3.49  
% 23.57/3.49  fof(f77,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f76])).
% 23.57/3.49  
% 23.57/3.49  fof(f160,plain,(
% 23.57/3.49    ( ! [X2,X0,X3,X1] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f77])).
% 23.57/3.49  
% 23.57/3.49  fof(f173,plain,(
% 23.57/3.49    v17_lattices(sK5)),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f172,plain,(
% 23.57/3.49    v10_lattices(sK5)),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f2,axiom,(
% 23.57/3.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f37,plain,(
% 23.57/3.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 23.57/3.49    inference(ennf_transformation,[],[f2])).
% 23.57/3.49  
% 23.57/3.49  fof(f38,plain,(
% 23.57/3.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 23.57/3.49    inference(flattening,[],[f37])).
% 23.57/3.49  
% 23.57/3.49  fof(f121,plain,(
% 23.57/3.49    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f38])).
% 23.57/3.49  
% 23.57/3.49  fof(f5,axiom,(
% 23.57/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f43,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f5])).
% 23.57/3.49  
% 23.57/3.49  fof(f44,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f43])).
% 23.57/3.49  
% 23.57/3.49  fof(f133,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f44])).
% 23.57/3.49  
% 23.57/3.49  fof(f12,axiom,(
% 23.57/3.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f57,plain,(
% 23.57/3.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 23.57/3.49    inference(ennf_transformation,[],[f12])).
% 23.57/3.49  
% 23.57/3.49  fof(f148,plain,(
% 23.57/3.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f57])).
% 23.57/3.49  
% 23.57/3.49  fof(f31,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f94,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f31])).
% 23.57/3.49  
% 23.57/3.49  fof(f95,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f94])).
% 23.57/3.49  
% 23.57/3.49  fof(f169,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f95])).
% 23.57/3.49  
% 23.57/3.49  fof(f123,plain,(
% 23.57/3.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f38])).
% 23.57/3.49  
% 23.57/3.49  fof(f147,plain,(
% 23.57/3.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f57])).
% 23.57/3.49  
% 23.57/3.49  fof(f6,axiom,(
% 23.57/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f45,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f6])).
% 23.57/3.49  
% 23.57/3.49  fof(f46,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f45])).
% 23.57/3.49  
% 23.57/3.49  fof(f134,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f46])).
% 23.57/3.49  
% 23.57/3.49  fof(f28,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f88,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f28])).
% 23.57/3.49  
% 23.57/3.49  fof(f89,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f88])).
% 23.57/3.49  
% 23.57/3.49  fof(f166,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f89])).
% 23.57/3.49  
% 23.57/3.49  fof(f30,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f92,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f30])).
% 23.57/3.49  
% 23.57/3.49  fof(f93,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f92])).
% 23.57/3.49  
% 23.57/3.49  fof(f168,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f93])).
% 23.57/3.49  
% 23.57/3.49  fof(f9,axiom,(
% 23.57/3.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f51,plain,(
% 23.57/3.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f9])).
% 23.57/3.49  
% 23.57/3.49  fof(f52,plain,(
% 23.57/3.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f51])).
% 23.57/3.49  
% 23.57/3.49  fof(f144,plain,(
% 23.57/3.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f52])).
% 23.57/3.49  
% 23.57/3.49  fof(f132,plain,(
% 23.57/3.49    ( ! [X0] : (v15_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f42])).
% 23.57/3.49  
% 23.57/3.49  fof(f3,axiom,(
% 23.57/3.49    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f39,plain,(
% 23.57/3.49    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 23.57/3.49    inference(ennf_transformation,[],[f3])).
% 23.57/3.49  
% 23.57/3.49  fof(f40,plain,(
% 23.57/3.49    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 23.57/3.49    inference(flattening,[],[f39])).
% 23.57/3.49  
% 23.57/3.49  fof(f128,plain,(
% 23.57/3.49    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f40])).
% 23.57/3.49  
% 23.57/3.49  fof(f24,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f80,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f24])).
% 23.57/3.49  
% 23.57/3.49  fof(f81,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f80])).
% 23.57/3.49  
% 23.57/3.49  fof(f162,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f81])).
% 23.57/3.49  
% 23.57/3.49  fof(f29,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f90,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f29])).
% 23.57/3.49  
% 23.57/3.49  fof(f91,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f90])).
% 23.57/3.49  
% 23.57/3.49  fof(f167,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f91])).
% 23.57/3.49  
% 23.57/3.49  fof(f10,axiom,(
% 23.57/3.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f53,plain,(
% 23.57/3.49    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f10])).
% 23.57/3.49  
% 23.57/3.49  fof(f54,plain,(
% 23.57/3.49    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f53])).
% 23.57/3.49  
% 23.57/3.49  fof(f145,plain,(
% 23.57/3.49    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f54])).
% 23.57/3.49  
% 23.57/3.49  fof(f129,plain,(
% 23.57/3.49    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f40])).
% 23.57/3.49  
% 23.57/3.49  fof(f26,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f84,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f26])).
% 23.57/3.49  
% 23.57/3.49  fof(f85,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f84])).
% 23.57/3.49  
% 23.57/3.49  fof(f164,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f85])).
% 23.57/3.49  
% 23.57/3.49  fof(f27,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f86,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f27])).
% 23.57/3.49  
% 23.57/3.49  fof(f87,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f86])).
% 23.57/3.49  
% 23.57/3.49  fof(f165,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k3_lattices(X0,k6_lattices(X0),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f87])).
% 23.57/3.49  
% 23.57/3.49  fof(f15,axiom,(
% 23.57/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f62,plain,(
% 23.57/3.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f15])).
% 23.57/3.49  
% 23.57/3.49  fof(f63,plain,(
% 23.57/3.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f62])).
% 23.57/3.49  
% 23.57/3.49  fof(f111,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(nnf_transformation,[],[f63])).
% 23.57/3.49  
% 23.57/3.49  fof(f151,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f111])).
% 23.57/3.49  
% 23.57/3.49  fof(f177,plain,(
% 23.57/3.49    r3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  fof(f125,plain,(
% 23.57/3.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f38])).
% 23.57/3.49  
% 23.57/3.49  fof(f126,plain,(
% 23.57/3.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f38])).
% 23.57/3.49  
% 23.57/3.49  fof(f18,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f68,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f18])).
% 23.57/3.49  
% 23.57/3.49  fof(f69,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f68])).
% 23.57/3.49  
% 23.57/3.49  fof(f112,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(nnf_transformation,[],[f69])).
% 23.57/3.49  
% 23.57/3.49  fof(f155,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f112])).
% 23.57/3.49  
% 23.57/3.49  fof(f14,axiom,(
% 23.57/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f60,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f14])).
% 23.57/3.49  
% 23.57/3.49  fof(f61,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f60])).
% 23.57/3.49  
% 23.57/3.49  fof(f150,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f61])).
% 23.57/3.49  
% 23.57/3.49  fof(f13,axiom,(
% 23.57/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f58,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f13])).
% 23.57/3.49  
% 23.57/3.49  fof(f59,plain,(
% 23.57/3.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f58])).
% 23.57/3.49  
% 23.57/3.49  fof(f149,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f59])).
% 23.57/3.49  
% 23.57/3.49  fof(f8,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f49,plain,(
% 23.57/3.49    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f8])).
% 23.57/3.49  
% 23.57/3.49  fof(f50,plain,(
% 23.57/3.49    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f49])).
% 23.57/3.49  
% 23.57/3.49  fof(f106,plain,(
% 23.57/3.49    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(nnf_transformation,[],[f50])).
% 23.57/3.49  
% 23.57/3.49  fof(f107,plain,(
% 23.57/3.49    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(rectify,[],[f106])).
% 23.57/3.49  
% 23.57/3.49  fof(f109,plain,(
% 23.57/3.49    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1 & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 23.57/3.49    introduced(choice_axiom,[])).
% 23.57/3.49  
% 23.57/3.49  fof(f108,plain,(
% 23.57/3.49    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) != sK3(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 23.57/3.49    introduced(choice_axiom,[])).
% 23.57/3.49  
% 23.57/3.49  fof(f110,plain,(
% 23.57/3.49    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != sK3(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f107,f109,f108])).
% 23.57/3.49  
% 23.57/3.49  fof(f140,plain,(
% 23.57/3.49    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f110])).
% 23.57/3.49  
% 23.57/3.49  fof(f32,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)))))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f96,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f32])).
% 23.57/3.49  
% 23.57/3.49  fof(f97,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (! [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f96])).
% 23.57/3.49  
% 23.57/3.49  fof(f170,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f97])).
% 23.57/3.49  
% 23.57/3.49  fof(f16,axiom,(
% 23.57/3.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 23.57/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.57/3.49  
% 23.57/3.49  fof(f64,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 23.57/3.49    inference(ennf_transformation,[],[f16])).
% 23.57/3.49  
% 23.57/3.49  fof(f65,plain,(
% 23.57/3.49    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 23.57/3.49    inference(flattening,[],[f64])).
% 23.57/3.49  
% 23.57/3.49  fof(f153,plain,(
% 23.57/3.49    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f65])).
% 23.57/3.49  
% 23.57/3.49  fof(f156,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f112])).
% 23.57/3.49  
% 23.57/3.49  fof(f152,plain,(
% 23.57/3.49    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 23.57/3.49    inference(cnf_transformation,[],[f111])).
% 23.57/3.49  
% 23.57/3.49  fof(f178,plain,(
% 23.57/3.49    ~r3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)),
% 23.57/3.49    inference(cnf_transformation,[],[f118])).
% 23.57/3.49  
% 23.57/3.49  cnf(c_55,negated_conjecture,
% 23.57/3.49      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.57/3.49      inference(cnf_transformation,[],[f175]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3492,plain,
% 23.57/3.49      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_27,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1) ),
% 23.57/3.49      inference(cnf_transformation,[],[f146]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_59,negated_conjecture,
% 23.57/3.49      ( ~ v2_struct_0(sK5) ),
% 23.57/3.49      inference(cnf_transformation,[],[f171]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2700,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | sK5 != X1 ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_27,c_59]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2701,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5))
% 23.57/3.49      | ~ l3_lattices(sK5) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_2700]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_56,negated_conjecture,
% 23.57/3.49      ( l3_lattices(sK5) ),
% 23.57/3.49      inference(cnf_transformation,[],[f174]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2705,plain,
% 23.57/3.49      ( m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 23.57/3.49      inference(global_propositional_subsumption,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_2701,c_56]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2706,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5)) ),
% 23.57/3.49      inference(renaming,[status(thm)],[c_2705]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3463,plain,
% 23.57/3.49      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(k7_lattices(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_2706]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_54,negated_conjecture,
% 23.57/3.49      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 23.57/3.49      inference(cnf_transformation,[],[f176]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3493,plain,
% 23.57/3.49      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_12,plain,
% 23.57/3.49      ( v11_lattices(X0)
% 23.57/3.49      | ~ v17_lattices(X0)
% 23.57/3.49      | ~ l3_lattices(X0)
% 23.57/3.49      | v2_struct_0(X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f131]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_41,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 23.57/3.49      | ~ v11_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
% 23.57/3.49      inference(cnf_transformation,[],[f160]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1061,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 23.57/3.49      | ~ v17_lattices(X4)
% 23.57/3.49      | ~ l3_lattices(X4)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X4)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | X1 != X4
% 23.57/3.49      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_12,c_41]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1062,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 23.57/3.49      | ~ v17_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_1061]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_57,negated_conjecture,
% 23.57/3.49      ( v17_lattices(sK5) ),
% 23.57/3.49      inference(cnf_transformation,[],[f173]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1968,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
% 23.57/3.49      | sK5 != X1 ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_1062,c_57]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1969,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 23.57/3.49      | ~ l3_lattices(sK5)
% 23.57/3.49      | v2_struct_0(sK5)
% 23.57/3.49      | ~ v10_lattices(sK5)
% 23.57/3.49      | k4_lattices(sK5,k3_lattices(sK5,X1,X2),k3_lattices(sK5,X1,X0)) = k3_lattices(sK5,X1,k4_lattices(sK5,X2,X0)) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_1968]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_58,negated_conjecture,
% 23.57/3.49      ( v10_lattices(sK5) ),
% 23.57/3.49      inference(cnf_transformation,[],[f172]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1973,plain,
% 23.57/3.49      ( ~ m1_subset_1(X2,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | k4_lattices(sK5,k3_lattices(sK5,X1,X2),k3_lattices(sK5,X1,X0)) = k3_lattices(sK5,X1,k4_lattices(sK5,X2,X0)) ),
% 23.57/3.49      inference(global_propositional_subsumption,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_1969,c_59,c_58,c_56]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1974,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 23.57/3.49      | k4_lattices(sK5,k3_lattices(sK5,X2,X0),k3_lattices(sK5,X2,X1)) = k3_lattices(sK5,X2,k4_lattices(sK5,X0,X1)) ),
% 23.57/3.49      inference(renaming,[status(thm)],[c_1973]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3489,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,X0,X1),k3_lattices(sK5,X0,X2)) = k3_lattices(sK5,X0,k4_lattices(sK5,X1,X2))
% 23.57/3.49      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7823,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,X0),X1),k3_lattices(sK5,k7_lattices(sK5,X0),X2)) = k3_lattices(sK5,k7_lattices(sK5,X0),k4_lattices(sK5,X1,X2))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3463,c_3489]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_81268,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),X0),k3_lattices(sK5,k7_lattices(sK5,sK7),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,X0,X1))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3493,c_7823]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_81286,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),sK6),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,X0))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3492,c_81268]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_6,plain,
% 23.57/3.49      ( v4_lattices(X0)
% 23.57/3.49      | ~ l3_lattices(X0)
% 23.57/3.49      | v2_struct_0(X0)
% 23.57/3.49      | ~ v10_lattices(X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f121]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_14,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l2_lattices(X1)
% 23.57/3.49      | ~ v4_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f133]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_806,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l2_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X3)
% 23.57/3.49      | v2_struct_0(X3)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X3)
% 23.57/3.49      | X1 != X3
% 23.57/3.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_807,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l2_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_806]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_28,plain,
% 23.57/3.49      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f148]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_825,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 23.57/3.49      inference(forward_subsumption_resolution,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_807,c_28]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2439,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 23.57/3.49      | sK5 != X1 ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_825,c_58]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2440,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ l3_lattices(sK5)
% 23.57/3.49      | v2_struct_0(sK5)
% 23.57/3.49      | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_2439]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2444,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
% 23.57/3.49      inference(global_propositional_subsumption,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_2440,c_59,c_56]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3469,plain,
% 23.57/3.49      ( k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0)
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_2444]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_6605,plain,
% 23.57/3.49      ( k3_lattices(sK5,X0,sK6) = k3_lattices(sK5,sK6,X0)
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3492,c_3469]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7213,plain,
% 23.57/3.49      ( k3_lattices(sK5,k7_lattices(sK5,X0),sK6) = k3_lattices(sK5,sK6,k7_lattices(sK5,X0))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3463,c_6605]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_20310,plain,
% 23.57/3.49      ( k3_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3493,c_7213]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_81292,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,X0))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(light_normalisation,[status(thm)],[c_81286,c_20310]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_82017,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,k7_lattices(sK5,X0)))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3463,c_81292]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_99449,plain,
% 23.57/3.49      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,k7_lattices(sK5,sK6))) ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3492,c_82017]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_50,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ v17_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0)) ),
% 23.57/3.49      inference(cnf_transformation,[],[f169]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2109,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0))
% 23.57/3.49      | sK5 != X1 ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_50,c_57]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2110,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ l3_lattices(sK5)
% 23.57/3.49      | v2_struct_0(sK5)
% 23.57/3.49      | ~ v10_lattices(sK5)
% 23.57/3.49      | k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1)) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_2109]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2114,plain,
% 23.57/3.49      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1)) ),
% 23.57/3.49      inference(global_propositional_subsumption,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_2110,c_59,c_58,c_56]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2115,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1)) ),
% 23.57/3.49      inference(renaming,[status(thm)],[c_2114]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3482,plain,
% 23.57/3.49      ( k3_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k4_lattices(sK5,X0,X1))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_2115]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7597,plain,
% 23.57/3.49      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)) = k7_lattices(sK5,k4_lattices(sK5,sK7,X0))
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3493,c_3482]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7619,plain,
% 23.57/3.49      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6)) = k7_lattices(sK5,k4_lattices(sK5,sK7,sK6)) ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3492,c_7597]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_4,plain,
% 23.57/3.49      ( v6_lattices(X0)
% 23.57/3.49      | ~ l3_lattices(X0)
% 23.57/3.49      | v2_struct_0(X0)
% 23.57/3.49      | ~ v10_lattices(X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f123]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_29,plain,
% 23.57/3.49      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f147]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_15,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l1_lattices(X1)
% 23.57/3.49      | ~ v6_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 23.57/3.49      inference(cnf_transformation,[],[f134]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1362,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ v6_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X3)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | X1 != X3
% 23.57/3.49      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_29,c_15]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1363,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ v6_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_1362]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1461,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X3)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X3)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X3)
% 23.57/3.49      | X1 != X3
% 23.57/3.49      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_4,c_1363]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_1462,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_1461]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2418,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 23.57/3.49      | sK5 != X1 ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_1462,c_58]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2419,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | ~ l3_lattices(sK5)
% 23.57/3.49      | v2_struct_0(sK5)
% 23.57/3.49      | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_2418]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2423,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.49      | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
% 23.57/3.49      inference(global_propositional_subsumption,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_2419,c_59,c_56]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3470,plain,
% 23.57/3.49      ( k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0)
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.49      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_2423]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7226,plain,
% 23.57/3.49      ( k4_lattices(sK5,X0,sK7) = k4_lattices(sK5,sK7,X0)
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3493,c_3470]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7248,plain,
% 23.57/3.49      ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3492,c_7226]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_7625,plain,
% 23.57/3.49      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6)) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
% 23.57/3.49      inference(light_normalisation,[status(thm)],[c_7619,c_7248]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_47,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ v17_lattices(X1)
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1) ),
% 23.57/3.49      inference(cnf_transformation,[],[f166]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2166,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.49      | ~ l3_lattices(X1)
% 23.57/3.49      | v2_struct_0(X1)
% 23.57/3.49      | ~ v10_lattices(X1)
% 23.57/3.49      | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
% 23.57/3.49      | sK5 != X1 ),
% 23.57/3.49      inference(resolution_lifted,[status(thm)],[c_47,c_57]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2167,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | ~ l3_lattices(sK5)
% 23.57/3.49      | v2_struct_0(sK5)
% 23.57/3.49      | ~ v10_lattices(sK5)
% 23.57/3.49      | k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5) ),
% 23.57/3.49      inference(unflattening,[status(thm)],[c_2166]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_2171,plain,
% 23.57/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.49      | k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5) ),
% 23.57/3.49      inference(global_propositional_subsumption,
% 23.57/3.49                [status(thm)],
% 23.57/3.49                [c_2167,c_59,c_58,c_56]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_3479,plain,
% 23.57/3.49      ( k4_lattices(sK5,k7_lattices(sK5,X0),X0) = k5_lattices(sK5)
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_5855,plain,
% 23.57/3.49      ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,X0)),k7_lattices(sK5,X0)) = k5_lattices(sK5)
% 23.57/3.49      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.49      inference(superposition,[status(thm)],[c_3463,c_3479]) ).
% 23.57/3.49  
% 23.57/3.49  cnf(c_19481,plain,
% 23.57/3.49      ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,sK6)),k7_lattices(sK5,sK6)) = k5_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_5855]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_49,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
% 23.57/3.50      inference(cnf_transformation,[],[f168]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2130,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k7_lattices(X1,k7_lattices(X1,X0)) = X0
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_49,c_57]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2131,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | k7_lattices(sK5,k7_lattices(sK5,X0)) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2130]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2135,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k7_lattices(sK5,k7_lattices(sK5,X0)) = X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2131,c_59,c_58,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3481,plain,
% 23.57/3.50      ( k7_lattices(sK5,k7_lattices(sK5,X0)) = X0
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4829,plain,
% 23.57/3.50      ( k7_lattices(sK5,k7_lattices(sK5,sK6)) = sK6 ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3481]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_19487,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK6)) = k5_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_19481,c_4829]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_25,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 23.57/3.50      | ~ l1_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f144]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1229,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(resolution,[status(thm)],[c_29,c_25]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2648,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_1229,c_59]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2649,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2648]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_133,plain,
% 23.57/3.50      ( l1_lattices(sK5) | ~ l3_lattices(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_29]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_145,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5))
% 23.57/3.50      | ~ l1_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_25]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2651,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2649,c_59,c_56,c_133,c_145]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3466,plain,
% 23.57/3.50      ( m1_subset_1(k5_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6607,plain,
% 23.57/3.50      ( k3_lattices(sK5,X0,k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3466,c_3469]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_14020,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,X0),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_6607]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_29333,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,sK7)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_14020]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_11,plain,
% 23.57/3.50      ( ~ v17_lattices(X0)
% 23.57/3.50      | v15_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f132]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_9,plain,
% 23.57/3.50      ( v13_lattices(X0)
% 23.57/3.50      | ~ v15_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f128]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_733,plain,
% 23.57/3.50      ( ~ v17_lattices(X0)
% 23.57/3.50      | v13_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(resolution,[status(thm)],[c_11,c_9]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_43,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v13_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
% 23.57/3.50      inference(cnf_transformation,[],[f162]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_993,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X2)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | X1 != X2
% 23.57/3.50      | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_733,c_43]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_994,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_993]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2016,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k5_lattices(X1),X0) = X0
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_994,c_57]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2017,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | k3_lattices(sK5,k5_lattices(sK5),X0) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2016]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2021,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k3_lattices(sK5,k5_lattices(sK5),X0) = X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2017,c_59,c_58,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3487,plain,
% 23.57/3.50      ( k3_lattices(sK5,k5_lattices(sK5),X0) = X0
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4874,plain,
% 23.57/3.50      ( k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,X0)) = k7_lattices(sK5,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3487]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_9234,plain,
% 23.57/3.50      ( k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_4874]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_29341,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k5_lattices(sK5)) = k7_lattices(sK5,sK7) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_29333,c_9234]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_99456,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k7_lattices(sK5,k4_lattices(sK5,sK6,sK7))) = k7_lattices(sK5,sK7) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_99449,c_7625,c_19487,c_29341]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_48,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1) ),
% 23.57/3.50      inference(cnf_transformation,[],[f167]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2148,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1)
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_48,c_57]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2149,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2148]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2153,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2149,c_59,c_58,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3480,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,X0),X0) = k6_lattices(sK5)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2153]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_5957,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,X0)),k7_lattices(sK5,X0)) = k6_lattices(sK5)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3480]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_19546,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,k5_lattices(sK5))),k7_lattices(sK5,k5_lattices(sK5))) = k6_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3466,c_5957]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4831,plain,
% 23.57/3.50      ( k7_lattices(sK5,k7_lattices(sK5,k5_lattices(sK5))) = k5_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3466,c_3481]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_9237,plain,
% 23.57/3.50      ( k3_lattices(sK5,k5_lattices(sK5),k7_lattices(sK5,k5_lattices(sK5))) = k7_lattices(sK5,k5_lattices(sK5)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3466,c_4874]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_19548,plain,
% 23.57/3.50      ( k7_lattices(sK5,k5_lattices(sK5)) = k6_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_19546,c_4831,c_9237]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_26,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 23.57/3.50      | ~ l2_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f145]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_879,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(resolution,[status(thm)],[c_28,c_26]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2659,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_879,c_59]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2660,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2659]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_136,plain,
% 23.57/3.50      ( l2_lattices(sK5) | ~ l3_lattices(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_28]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_142,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 23.57/3.50      | ~ l2_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_26]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2662,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2660,c_59,c_56,c_136,c_142]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3465,plain,
% 23.57/3.50      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2662]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_82015,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,sK6,k6_lattices(sK5))) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_81292]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7227,plain,
% 23.57/3.50      ( k4_lattices(sK5,X0,sK6) = k4_lattices(sK5,sK6,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3470]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7276,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k6_lattices(sK5)) = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_7227]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8,plain,
% 23.57/3.50      ( ~ v15_lattices(X0)
% 23.57/3.50      | v14_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f129]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_750,plain,
% 23.57/3.50      ( ~ v17_lattices(X0)
% 23.57/3.50      | v14_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0) ),
% 23.57/3.50      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_45,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v14_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
% 23.57/3.50      inference(cnf_transformation,[],[f164]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_931,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X2)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | X1 != X2
% 23.57/3.50      | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_750,c_45]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_932,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k4_lattices(X1,k6_lattices(X1),X0) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_931]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2052,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k4_lattices(X1,k6_lattices(X1),X0) = X0
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_932,c_57]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2053,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | k4_lattices(sK5,k6_lattices(sK5),X0) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2052]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2057,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k4_lattices(sK5,k6_lattices(sK5),X0) = X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2053,c_59,c_58,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3485,plain,
% 23.57/3.50      ( k4_lattices(sK5,k6_lattices(sK5),X0) = X0
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2057]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4840,plain,
% 23.57/3.50      ( k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6 ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3485]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7280,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k6_lattices(sK5)) = sK6 ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_7276,c_4840]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6606,plain,
% 23.57/3.50      ( k3_lattices(sK5,X0,k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_3469]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_13701,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,X0),k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_6606]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_29121,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,sK7)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_13701]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_46,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v14_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1) ),
% 23.57/3.50      inference(cnf_transformation,[],[f165]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_907,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X2)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | X1 != X2
% 23.57/3.50      | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1) ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_750,c_46]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_908,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_907]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2070,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k3_lattices(X1,k6_lattices(X1),X0) = k6_lattices(X1)
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_908,c_57]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2071,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | k3_lattices(sK5,k6_lattices(sK5),X0) = k6_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2070]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2075,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k3_lattices(sK5,k6_lattices(sK5),X0) = k6_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2071,c_59,c_58,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3484,plain,
% 23.57/3.50      ( k3_lattices(sK5,k6_lattices(sK5),X0) = k6_lattices(sK5)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2075]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_5733,plain,
% 23.57/3.50      ( k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,X0)) = k6_lattices(sK5)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3484]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8792,plain,
% 23.57/3.50      ( k3_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,sK7)) = k6_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_5733]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_29129,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5)) = k6_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_29121,c_8792]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_82019,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k6_lattices(sK5)) = k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_82015,c_7280,c_20310,c_29129]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_33,plain,
% 23.57/3.50      ( r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ r3_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ v6_lattices(X0)
% 23.57/3.50      | ~ v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v9_lattices(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f151]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_53,negated_conjecture,
% 23.57/3.50      ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(cnf_transformation,[],[f177]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_450,plain,
% 23.57/3.50      ( r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(prop_impl,[status(thm)],[c_53]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1204,plain,
% 23.57/3.50      ( r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ v6_lattices(X0)
% 23.57/3.50      | ~ v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v9_lattices(X0)
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | k7_lattices(sK5,sK7) != X2
% 23.57/3.50      | sK6 != X1
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_33,c_450]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1205,plain,
% 23.57/3.50      ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.57/3.50      | ~ v6_lattices(sK5)
% 23.57/3.50      | ~ v8_lattices(sK5)
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v9_lattices(sK5)
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_1204]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_202,plain,
% 23.57/3.50      ( v6_lattices(sK5)
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2,plain,
% 23.57/3.50      ( v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v10_lattices(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f125]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_208,plain,
% 23.57/3.50      ( v8_lattices(sK5)
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1,plain,
% 23.57/3.50      ( ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v10_lattices(X0)
% 23.57/3.50      | v9_lattices(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f126]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_211,plain,
% 23.57/3.50      ( ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | v9_lattices(sK5) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1207,plain,
% 23.57/3.50      ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_1205,c_59,c_58,c_56,c_55,c_202,c_208,c_211]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3490,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
% 23.57/3.50      | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_65,plain,
% 23.57/3.50      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1209,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
% 23.57/3.50      | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3584,plain,
% 23.57/3.50      ( m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 23.57/3.50      inference(instantiation,[status(thm)],[c_2706]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3585,plain,
% 23.57/3.50      ( m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) = iProver_top
% 23.57/3.50      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_3584]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8103,plain,
% 23.57/3.50      ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_3490,c_65,c_1209,c_3585]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8104,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top ),
% 23.57/3.50      inference(renaming,[status(thm)],[c_8103]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_37,plain,
% 23.57/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v9_lattices(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) = X1 ),
% 23.57/3.50      inference(cnf_transformation,[],[f155]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1598,plain,
% 23.57/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v10_lattices(X0)
% 23.57/3.50      | ~ v9_lattices(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) = X1 ),
% 23.57/3.50      inference(resolution,[status(thm)],[c_2,c_37]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1602,plain,
% 23.57/3.50      ( ~ v10_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | k2_lattices(X0,X1,X2) = X1 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_1598,c_37,c_2,c_1]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1603,plain,
% 23.57/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v10_lattices(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) = X1 ),
% 23.57/3.50      inference(renaming,[status(thm)],[c_1602]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2247,plain,
% 23.57/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) = X1
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_1603,c_58]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2248,plain,
% 23.57/3.50      ( ~ r1_lattices(sK5,X0,X1)
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | k2_lattices(sK5,X0,X1) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2247]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2252,plain,
% 23.57/3.50      ( ~ r1_lattices(sK5,X0,X1)
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,X0,X1) = X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2248,c_59,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2253,plain,
% 23.57/3.50      ( ~ r1_lattices(sK5,X0,X1)
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,X0,X1) = X0 ),
% 23.57/3.50      inference(renaming,[status(thm)],[c_2252]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3477,plain,
% 23.57/3.50      ( k2_lattices(sK5,X0,X1) = X0
% 23.57/3.50      | r1_lattices(sK5,X0,X1) != iProver_top
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2253]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8107,plain,
% 23.57/3.50      ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_8104,c_3477]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8108,plain,
% 23.57/3.50      ( ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_8107]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_93218,plain,
% 23.57/3.50      ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_8107,c_55,c_54,c_3584,c_8108]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_31,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l1_lattices(X1)
% 23.57/3.50      | ~ v6_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f150]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1311,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ v6_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X3)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | X1 != X3
% 23.57/3.50      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1312,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ v6_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_1311]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1485,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X3)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X3)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X3)
% 23.57/3.50      | X1 != X3
% 23.57/3.50      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_4,c_1312]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1486,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_1485]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2397,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_1486,c_58]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2398,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2397]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2402,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2398,c_59,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3471,plain,
% 23.57/3.50      ( k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2402]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7291,plain,
% 23.57/3.50      ( k2_lattices(sK5,sK6,X0) = k4_lattices(sK5,sK6,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3471]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7354,plain,
% 23.57/3.50      ( k2_lattices(sK5,sK6,k7_lattices(sK5,X0)) = k4_lattices(sK5,sK6,k7_lattices(sK5,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_7291]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_20913,plain,
% 23.57/3.50      ( k2_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_7354]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_93220,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(demodulation,[status(thm)],[c_93218,c_20913]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_81269,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),X0),k3_lattices(sK5,k7_lattices(sK5,sK6),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,X0,X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_7823]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_81519,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,X0)),k3_lattices(sK5,k7_lattices(sK5,sK6),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,X0),X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_81269]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_88619,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,sK7),X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_81519]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7598,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,X0)) = k7_lattices(sK5,k4_lattices(sK5,sK6,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3482]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7635,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,sK7)) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_7598]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_88628,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,sK7),X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_88619,c_7635]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_88696,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK6),sK6)) = k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,k7_lattices(sK5,sK7),sK6)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_88628]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_5954,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k6_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3480]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7278,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k7_lattices(sK5,X0)) = k4_lattices(sK5,k7_lattices(sK5,X0),sK6)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_7227]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_20395,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,sK7),sK6) = k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_7278]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_81289,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)),k3_lattices(sK5,k7_lattices(sK5,sK7),X1)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,X0),X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_81268]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_86831,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,sK6)),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,sK6),X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_81289]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_86838,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),X0)) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,sK6),X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_86831,c_7625]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_87318,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k3_lattices(sK5,k7_lattices(sK5,sK7),k6_lattices(sK5))) = k3_lattices(sK5,k7_lattices(sK5,sK7),k4_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5))) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_86838]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7294,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,X0),X1) = k4_lattices(sK5,k7_lattices(sK5,X0),X1)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3471]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_23842,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,sK6),X0) = k4_lattices(sK5,k7_lattices(sK5,sK6),X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_7294]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_23872,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) = k4_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_23842]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_30,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l2_lattices(X1)
% 23.57/3.50      | ~ v4_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f149]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_777,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l2_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X3)
% 23.57/3.50      | v2_struct_0(X3)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X3)
% 23.57/3.50      | X1 != X3
% 23.57/3.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_778,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l2_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_777]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_796,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 23.57/3.50      inference(forward_subsumption_resolution,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_778,c_28]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2460,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_796,c_58]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2461,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2460]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2465,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2461,c_59,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3468,plain,
% 23.57/3.50      ( k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2465]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6587,plain,
% 23.57/3.50      ( k1_lattices(sK5,k7_lattices(sK5,X0),X1) = k3_lattices(sK5,k7_lattices(sK5,X0),X1)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3468]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_21276,plain,
% 23.57/3.50      ( k1_lattices(sK5,k7_lattices(sK5,sK6),X0) = k3_lattices(sK5,k7_lattices(sK5,sK6),X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_6587]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_21351,plain,
% 23.57/3.50      ( k1_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_21276]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_21355,plain,
% 23.57/3.50      ( k1_lattices(sK5,k7_lattices(sK5,sK6),sK6) = k6_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_21351,c_5954]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_24,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v9_lattices(X1)
% 23.57/3.50      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 23.57/3.50      inference(cnf_transformation,[],[f140]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2718,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | ~ v9_lattices(X1)
% 23.57/3.50      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_24,c_59]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2719,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | ~ v9_lattices(sK5)
% 23.57/3.50      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2718]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2350,plain,
% 23.57/3.50      ( ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | v9_lattices(X0)
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_1,c_58]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2351,plain,
% 23.57/3.50      ( ~ l3_lattices(sK5) | v2_struct_0(sK5) | v9_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2350]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2353,plain,
% 23.57/3.50      ( v9_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2351,c_59,c_58,c_56,c_211]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2598,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_24,c_2353]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2599,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2598]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2723,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2719,c_59,c_56,c_2599]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3467,plain,
% 23.57/3.50      ( k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2723]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_5864,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,X0),k1_lattices(sK5,k7_lattices(sK5,X0),X1)) = k7_lattices(sK5,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3467]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_20515,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,sK6),k1_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k7_lattices(sK5,sK6)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_5864]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_20604,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,sK6),k1_lattices(sK5,k7_lattices(sK5,sK6),sK6)) = k7_lattices(sK5,sK6) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_20515]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_21383,plain,
% 23.57/3.50      ( k2_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) = k7_lattices(sK5,sK6) ),
% 23.57/3.50      inference(demodulation,[status(thm)],[c_21355,c_20604]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_23875,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,sK6),k6_lattices(sK5)) = k7_lattices(sK5,sK6) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_23872,c_21383]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_87322,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)),k6_lattices(sK5)) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_87318,c_7625,c_23875,c_29129]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_88702,plain,
% 23.57/3.50      ( k3_lattices(sK5,k7_lattices(sK5,sK6),k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_88696,c_5954,c_20395,c_87322]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_93224,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) = k3_lattices(sK5,k7_lattices(sK5,sK6),sK6) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_93220,c_88702]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_93244,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | k7_lattices(sK5,k4_lattices(sK5,sK6,sK7)) = k6_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_93224,c_5954]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_51,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ v17_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
% 23.57/3.50      inference(cnf_transformation,[],[f170]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2088,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_51,c_57]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2089,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v10_lattices(sK5)
% 23.57/3.50      | k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1)) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2088]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2093,plain,
% 23.57/3.50      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1)) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2089,c_59,c_58,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2094,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1)) ),
% 23.57/3.50      inference(renaming,[status(thm)],[c_2093]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3483,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,X0),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,X0,X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7658,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,X0)),k7_lattices(sK5,X1)) = k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,X0),X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3483]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_67663,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,sK6)),k7_lattices(sK5,X0)) = k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_7658]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_67669,plain,
% 23.57/3.50      ( k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),X0)) = k4_lattices(sK5,sK6,k7_lattices(sK5,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_67663,c_4829]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_67685,plain,
% 23.57/3.50      ( k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,X0))) = k4_lattices(sK5,sK6,k7_lattices(sK5,k7_lattices(sK5,X0)))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_67669]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_67943,plain,
% 23.57/3.50      ( k7_lattices(sK5,k3_lattices(sK5,k7_lattices(sK5,sK6),k7_lattices(sK5,sK7))) = k4_lattices(sK5,sK6,k7_lattices(sK5,k7_lattices(sK5,sK7))) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_67685]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4828,plain,
% 23.57/3.50      ( k7_lattices(sK5,k7_lattices(sK5,sK7)) = sK7 ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_3481]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_67951,plain,
% 23.57/3.50      ( k7_lattices(sK5,k7_lattices(sK5,k4_lattices(sK5,sK6,sK7))) = k4_lattices(sK5,sK6,sK7) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_67943,c_4828,c_7635]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_93270,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5)
% 23.57/3.50      | k7_lattices(sK5,k6_lattices(sK5)) = k4_lattices(sK5,sK6,sK7) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_93244,c_67951]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_19482,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,k7_lattices(sK5,k6_lattices(sK5))),k7_lattices(sK5,k6_lattices(sK5))) = k5_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_5855]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4830,plain,
% 23.57/3.50      ( k7_lattices(sK5,k7_lattices(sK5,k6_lattices(sK5))) = k6_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_3481]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4843,plain,
% 23.57/3.50      ( k4_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,X0)) = k7_lattices(sK5,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_3485]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_8803,plain,
% 23.57/3.50      ( k4_lattices(sK5,k6_lattices(sK5),k7_lattices(sK5,k6_lattices(sK5))) = k7_lattices(sK5,k6_lattices(sK5)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_4843]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_19486,plain,
% 23.57/3.50      ( k7_lattices(sK5,k6_lattices(sK5)) = k5_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_19482,c_4830,c_8803]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_93273,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,sK7) = k5_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_93270,c_19486]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_99457,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = k7_lattices(sK5,sK7) ),
% 23.57/3.50      inference(demodulation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_99456,c_19548,c_82019,c_93273]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7820,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,X0),k3_lattices(sK5,sK6,X1)) = k3_lattices(sK5,sK6,k4_lattices(sK5,X0,X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3489]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7871,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,X0)),k3_lattices(sK5,sK6,X1)) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,X0),X1))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_7820]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_82969,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,X0)) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_7871]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_82991,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,k7_lattices(sK5,X0))) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_82969]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_84257,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,k7_lattices(sK5,k6_lattices(sK5)))) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,k6_lattices(sK5)))) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_82991]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7212,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK6,k5_lattices(sK5)) = k3_lattices(sK5,k5_lattices(sK5),sK6) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3466,c_6605]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4871,plain,
% 23.57/3.50      ( k3_lattices(sK5,k5_lattices(sK5),sK6) = sK6 ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3487]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7214,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK6,k5_lattices(sK5)) = sK6 ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_7212,c_4871]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7654,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,X0)) = k7_lattices(sK5,k3_lattices(sK5,sK7,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_3483]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7677,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,k6_lattices(sK5))) = k7_lattices(sK5,k3_lattices(sK5,sK7,k6_lattices(sK5))) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_7654]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6604,plain,
% 23.57/3.50      ( k3_lattices(sK5,X0,sK7) = k3_lattices(sK5,sK7,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_3469]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7139,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK7,k6_lattices(sK5)) = k3_lattices(sK5,k6_lattices(sK5),sK7) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3465,c_6604]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_5729,plain,
% 23.57/3.50      ( k3_lattices(sK5,k6_lattices(sK5),sK7) = k6_lattices(sK5) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_3484]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7143,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK7,k6_lattices(sK5)) = k6_lattices(sK5) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_7139,c_5729]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7681,plain,
% 23.57/3.50      ( k4_lattices(sK5,k7_lattices(sK5,sK7),k7_lattices(sK5,k6_lattices(sK5))) = k7_lattices(sK5,k6_lattices(sK5)) ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_7677,c_7143]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_82988,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),k3_lattices(sK5,sK6,sK6)) = k3_lattices(sK5,sK6,k4_lattices(sK5,k7_lattices(sK5,sK7),sK6)) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_82969]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6584,plain,
% 23.57/3.50      ( k1_lattices(sK5,sK6,X0) = k3_lattices(sK5,sK6,X0)
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3468]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6979,plain,
% 23.57/3.50      ( k1_lattices(sK5,sK6,sK6) = k3_lattices(sK5,sK6,sK6) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_6584]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_34,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v6_lattices(X1)
% 23.57/3.50      | ~ v8_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v9_lattices(X1)
% 23.57/3.50      | k1_lattices(X1,X0,X0) = X0 ),
% 23.57/3.50      inference(cnf_transformation,[],[f153]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1537,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v8_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X2)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X2)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X2)
% 23.57/3.50      | ~ v9_lattices(X1)
% 23.57/3.50      | X1 != X2
% 23.57/3.50      | k1_lattices(X1,X0,X0) = X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_4,c_34]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1538,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ v8_lattices(X1)
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | ~ v9_lattices(X1)
% 23.57/3.50      | k1_lattices(X1,X0,X0) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_1537]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1556,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | ~ v10_lattices(X1)
% 23.57/3.50      | k1_lattices(X1,X0,X0) = X0 ),
% 23.57/3.50      inference(forward_subsumption_resolution,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_1538,c_1,c_2]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2361,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.57/3.50      | ~ l3_lattices(X1)
% 23.57/3.50      | v2_struct_0(X1)
% 23.57/3.50      | k1_lattices(X1,X0,X0) = X0
% 23.57/3.50      | sK5 != X1 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_1556,c_58]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2362,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | k1_lattices(sK5,X0,X0) = X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2361]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2366,plain,
% 23.57/3.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k1_lattices(sK5,X0,X0) = X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2362,c_59,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3473,plain,
% 23.57/3.50      ( k1_lattices(sK5,X0,X0) = X0
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_4076,plain,
% 23.57/3.50      ( k1_lattices(sK5,sK6,sK6) = sK6 ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_3473]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_6983,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK6,sK6) = sK6 ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_6979,c_4076]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_82994,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7)),sK6) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_82988,c_6983,c_20395]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_84261,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k3_lattices(sK5,sK6,k7_lattices(sK5,k6_lattices(sK5))) ),
% 23.57/3.50      inference(light_normalisation,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_84257,c_7214,c_7681,c_19486,c_82994]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_84262,plain,
% 23.57/3.50      ( k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = sK6 ),
% 23.57/3.50      inference(demodulation,[status(thm)],[c_84261,c_7214,c_19486]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7868,plain,
% 23.57/3.50      ( k4_lattices(sK5,k3_lattices(sK5,sK6,sK6),k3_lattices(sK5,sK6,X0)) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3492,c_7820]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_7874,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,X0)) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,X0))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(light_normalisation,[status(thm)],[c_7868,c_6983]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_23709,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,k7_lattices(sK5,X0))) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,X0)))
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3463,c_7874]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_37071,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = k3_lattices(sK5,sK6,k4_lattices(sK5,sK6,k7_lattices(sK5,sK7))) ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_3493,c_23709]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_99160,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k3_lattices(sK5,sK6,k7_lattices(sK5,sK7))) = sK6 ),
% 23.57/3.50      inference(demodulation,[status(thm)],[c_84262,c_37071]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_99655,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = sK6 ),
% 23.57/3.50      inference(demodulation,[status(thm)],[c_99457,c_99160]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_36,plain,
% 23.57/3.50      ( r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v9_lattices(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) != X1 ),
% 23.57/3.50      inference(cnf_transformation,[],[f156]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1630,plain,
% 23.57/3.50      ( r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v10_lattices(X0)
% 23.57/3.50      | ~ v9_lattices(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) != X1 ),
% 23.57/3.50      inference(resolution,[status(thm)],[c_2,c_36]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1634,plain,
% 23.57/3.50      ( ~ v10_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | r1_lattices(X0,X1,X2)
% 23.57/3.50      | k2_lattices(X0,X1,X2) != X1 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_1630,c_36,c_2,c_1]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1635,plain,
% 23.57/3.50      ( r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v10_lattices(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) != X1 ),
% 23.57/3.50      inference(renaming,[status(thm)],[c_1634]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2223,plain,
% 23.57/3.50      ( r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | k2_lattices(X0,X1,X2) != X1
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_1635,c_58]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2224,plain,
% 23.57/3.50      ( r1_lattices(sK5,X0,X1)
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | k2_lattices(sK5,X0,X1) != X0 ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_2223]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2228,plain,
% 23.57/3.50      ( r1_lattices(sK5,X0,X1)
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,X0,X1) != X0 ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_2224,c_59,c_56]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_2229,plain,
% 23.57/3.50      ( r1_lattices(sK5,X0,X1)
% 23.57/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.57/3.50      | k2_lattices(sK5,X0,X1) != X0 ),
% 23.57/3.50      inference(renaming,[status(thm)],[c_2228]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_3478,plain,
% 23.57/3.50      ( k2_lattices(sK5,X0,X1) != X0
% 23.57/3.50      | r1_lattices(sK5,X0,X1) = iProver_top
% 23.57/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(predicate_to_equality,[status(thm)],[c_2229]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_20925,plain,
% 23.57/3.50      ( k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != sK6
% 23.57/3.50      | r1_lattices(sK5,sK6,k7_lattices(sK5,sK7)) = iProver_top
% 23.57/3.50      | m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5)) != iProver_top
% 23.57/3.50      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.57/3.50      inference(superposition,[status(thm)],[c_20913,c_3478]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_20926,plain,
% 23.57/3.50      ( r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.57/3.50      | k4_lattices(sK5,sK6,k7_lattices(sK5,sK7)) != sK6 ),
% 23.57/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_20925]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_32,plain,
% 23.57/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | r3_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ v6_lattices(X0)
% 23.57/3.50      | ~ v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v9_lattices(X0) ),
% 23.57/3.50      inference(cnf_transformation,[],[f152]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_52,negated_conjecture,
% 23.57/3.50      ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
% 23.57/3.50      inference(cnf_transformation,[],[f178]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_448,plain,
% 23.57/3.50      ( ~ r3_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
% 23.57/3.50      inference(prop_impl,[status(thm)],[c_52]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1187,plain,
% 23.57/3.50      ( ~ r1_lattices(X0,X1,X2)
% 23.57/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.57/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.57/3.50      | ~ v6_lattices(X0)
% 23.57/3.50      | ~ v8_lattices(X0)
% 23.57/3.50      | ~ l3_lattices(X0)
% 23.57/3.50      | v2_struct_0(X0)
% 23.57/3.50      | ~ v9_lattices(X0)
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5)
% 23.57/3.50      | k7_lattices(sK5,sK7) != X2
% 23.57/3.50      | sK6 != X1
% 23.57/3.50      | sK5 != X0 ),
% 23.57/3.50      inference(resolution_lifted,[status(thm)],[c_32,c_448]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1188,plain,
% 23.57/3.50      ( ~ r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.57/3.50      | ~ v6_lattices(sK5)
% 23.57/3.50      | ~ v8_lattices(sK5)
% 23.57/3.50      | ~ l3_lattices(sK5)
% 23.57/3.50      | v2_struct_0(sK5)
% 23.57/3.50      | ~ v9_lattices(sK5)
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
% 23.57/3.50      inference(unflattening,[status(thm)],[c_1187]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(c_1190,plain,
% 23.57/3.50      ( ~ r1_lattices(sK5,sK6,k7_lattices(sK5,sK7))
% 23.57/3.50      | ~ m1_subset_1(k7_lattices(sK5,sK7),u1_struct_0(sK5))
% 23.57/3.50      | k4_lattices(sK5,sK6,sK7) != k5_lattices(sK5) ),
% 23.57/3.50      inference(global_propositional_subsumption,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_1188,c_59,c_58,c_56,c_55,c_202,c_208,c_211]) ).
% 23.57/3.50  
% 23.57/3.50  cnf(contradiction,plain,
% 23.57/3.50      ( $false ),
% 23.57/3.50      inference(minisat,
% 23.57/3.50                [status(thm)],
% 23.57/3.50                [c_99655,c_93273,c_20926,c_3584,c_1190,c_54,c_55]) ).
% 23.57/3.50  
% 23.57/3.50  
% 23.57/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.57/3.50  
% 23.57/3.50  ------                               Statistics
% 23.57/3.50  
% 23.57/3.50  ------ General
% 23.57/3.50  
% 23.57/3.50  abstr_ref_over_cycles:                  0
% 23.57/3.50  abstr_ref_under_cycles:                 0
% 23.57/3.50  gc_basic_clause_elim:                   0
% 23.57/3.50  forced_gc_time:                         0
% 23.57/3.50  parsing_time:                           0.013
% 23.57/3.50  unif_index_cands_time:                  0.
% 23.57/3.50  unif_index_add_time:                    0.
% 23.57/3.50  orderings_time:                         0.
% 23.57/3.50  out_proof_time:                         0.035
% 23.57/3.50  total_time:                             2.891
% 23.57/3.50  num_of_symbols:                         67
% 23.57/3.50  num_of_terms:                           94258
% 23.57/3.50  
% 23.57/3.50  ------ Preprocessing
% 23.57/3.50  
% 23.57/3.50  num_of_splits:                          0
% 23.57/3.50  num_of_split_atoms:                     0
% 23.57/3.50  num_of_reused_defs:                     0
% 23.57/3.50  num_eq_ax_congr_red:                    32
% 23.57/3.50  num_of_sem_filtered_clauses:            1
% 23.57/3.50  num_of_subtypes:                        0
% 23.57/3.50  monotx_restored_types:                  0
% 23.57/3.50  sat_num_of_epr_types:                   0
% 23.57/3.50  sat_num_of_non_cyclic_types:            0
% 23.57/3.50  sat_guarded_non_collapsed_types:        0
% 23.57/3.50  num_pure_diseq_elim:                    0
% 23.57/3.50  simp_replaced_by:                       0
% 23.57/3.50  res_preprocessed:                       178
% 23.57/3.50  prep_upred:                             0
% 23.57/3.50  prep_unflattend:                        70
% 23.57/3.50  smt_new_axioms:                         0
% 23.57/3.50  pred_elim_cands:                        2
% 23.57/3.50  pred_elim:                              17
% 23.57/3.50  pred_elim_cl:                           25
% 23.57/3.50  pred_elim_cycles:                       22
% 23.57/3.50  merged_defs:                            2
% 23.57/3.50  merged_defs_ncl:                        0
% 23.57/3.50  bin_hyper_res:                          2
% 23.57/3.50  prep_cycles:                            4
% 23.57/3.50  pred_elim_time:                         0.047
% 23.57/3.50  splitting_time:                         0.
% 23.57/3.50  sem_filter_time:                        0.
% 23.57/3.50  monotx_time:                            0.
% 23.57/3.50  subtype_inf_time:                       0.
% 23.57/3.50  
% 23.57/3.50  ------ Problem properties
% 23.57/3.50  
% 23.57/3.50  clauses:                                32
% 23.57/3.50  conjectures:                            2
% 23.57/3.50  epr:                                    0
% 23.57/3.50  horn:                                   31
% 23.57/3.50  ground:                                 6
% 23.57/3.50  unary:                                  4
% 23.57/3.50  binary:                                 11
% 23.57/3.50  lits:                                   85
% 23.57/3.50  lits_eq:                                25
% 23.57/3.50  fd_pure:                                0
% 23.57/3.50  fd_pseudo:                              0
% 23.57/3.50  fd_cond:                                0
% 23.57/3.50  fd_pseudo_cond:                         1
% 23.57/3.50  ac_symbols:                             0
% 23.57/3.50  
% 23.57/3.50  ------ Propositional Solver
% 23.57/3.50  
% 23.57/3.50  prop_solver_calls:                      48
% 23.57/3.50  prop_fast_solver_calls:                 4006
% 23.57/3.50  smt_solver_calls:                       0
% 23.57/3.50  smt_fast_solver_calls:                  0
% 23.57/3.50  prop_num_of_clauses:                    35171
% 23.57/3.50  prop_preprocess_simplified:             77740
% 23.57/3.50  prop_fo_subsumed:                       270
% 23.57/3.50  prop_solver_time:                       0.
% 23.57/3.50  smt_solver_time:                        0.
% 23.57/3.50  smt_fast_solver_time:                   0.
% 23.57/3.50  prop_fast_solver_time:                  0.
% 23.57/3.50  prop_unsat_core_time:                   0.005
% 23.57/3.50  
% 23.57/3.50  ------ QBF
% 23.57/3.50  
% 23.57/3.50  qbf_q_res:                              0
% 23.57/3.50  qbf_num_tautologies:                    0
% 23.57/3.50  qbf_prep_cycles:                        0
% 23.57/3.50  
% 23.57/3.50  ------ BMC1
% 23.57/3.50  
% 23.57/3.50  bmc1_current_bound:                     -1
% 23.57/3.50  bmc1_last_solved_bound:                 -1
% 23.57/3.50  bmc1_unsat_core_size:                   -1
% 23.57/3.50  bmc1_unsat_core_parents_size:           -1
% 23.57/3.50  bmc1_merge_next_fun:                    0
% 23.57/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.57/3.50  
% 23.57/3.50  ------ Instantiation
% 23.57/3.50  
% 23.57/3.50  inst_num_of_clauses:                    3589
% 23.57/3.50  inst_num_in_passive:                    546
% 23.57/3.50  inst_num_in_active:                     4345
% 23.57/3.50  inst_num_in_unprocessed:                1289
% 23.57/3.50  inst_num_of_loops:                      4859
% 23.57/3.50  inst_num_of_learning_restarts:          1
% 23.57/3.50  inst_num_moves_active_passive:          507
% 23.57/3.50  inst_lit_activity:                      0
% 23.57/3.50  inst_lit_activity_moves:                6
% 23.57/3.50  inst_num_tautologies:                   0
% 23.57/3.50  inst_num_prop_implied:                  0
% 23.57/3.50  inst_num_existing_simplified:           0
% 23.57/3.50  inst_num_eq_res_simplified:             0
% 23.57/3.50  inst_num_child_elim:                    0
% 23.57/3.50  inst_num_of_dismatching_blockings:      18135
% 23.57/3.50  inst_num_of_non_proper_insts:           16399
% 23.57/3.50  inst_num_of_duplicates:                 0
% 23.57/3.50  inst_inst_num_from_inst_to_res:         0
% 23.57/3.50  inst_dismatching_checking_time:         0.
% 23.57/3.50  
% 23.57/3.50  ------ Resolution
% 23.57/3.50  
% 23.57/3.50  res_num_of_clauses:                     44
% 23.57/3.50  res_num_in_passive:                     44
% 23.57/3.50  res_num_in_active:                      0
% 23.57/3.50  res_num_of_loops:                       182
% 23.57/3.50  res_forward_subset_subsumed:            106
% 23.57/3.50  res_backward_subset_subsumed:           0
% 23.57/3.50  res_forward_subsumed:                   0
% 23.57/3.50  res_backward_subsumed:                  0
% 23.57/3.50  res_forward_subsumption_resolution:     6
% 23.57/3.50  res_backward_subsumption_resolution:    0
% 23.57/3.50  res_clause_to_clause_subsumption:       6671
% 23.57/3.50  res_orphan_elimination:                 0
% 23.57/3.50  res_tautology_del:                      943
% 23.57/3.50  res_num_eq_res_simplified:              0
% 23.57/3.50  res_num_sel_changes:                    0
% 23.57/3.50  res_moves_from_active_to_pass:          0
% 23.57/3.50  
% 23.57/3.50  ------ Superposition
% 23.57/3.50  
% 23.57/3.50  sup_time_total:                         0.
% 23.57/3.50  sup_time_generating:                    0.
% 23.57/3.50  sup_time_sim_full:                      0.
% 23.57/3.50  sup_time_sim_immed:                     0.
% 23.57/3.50  
% 23.57/3.50  sup_num_of_clauses:                     1273
% 23.57/3.50  sup_num_in_active:                      848
% 23.57/3.50  sup_num_in_passive:                     425
% 23.57/3.50  sup_num_of_loops:                       970
% 23.57/3.50  sup_fw_superposition:                   2869
% 23.57/3.50  sup_bw_superposition:                   385
% 23.57/3.50  sup_immediate_simplified:               2156
% 23.57/3.50  sup_given_eliminated:                   3
% 23.57/3.50  comparisons_done:                       0
% 23.57/3.50  comparisons_avoided:                    6
% 23.57/3.50  
% 23.57/3.50  ------ Simplifications
% 23.57/3.50  
% 23.57/3.50  
% 23.57/3.50  sim_fw_subset_subsumed:                 105
% 23.57/3.50  sim_bw_subset_subsumed:                 50
% 23.57/3.50  sim_fw_subsumed:                        36
% 23.57/3.50  sim_bw_subsumed:                        0
% 23.57/3.50  sim_fw_subsumption_res:                 0
% 23.57/3.50  sim_bw_subsumption_res:                 0
% 23.57/3.50  sim_tautology_del:                      20
% 23.57/3.50  sim_eq_tautology_del:                   1558
% 23.57/3.50  sim_eq_res_simp:                        4
% 23.57/3.50  sim_fw_demodulated:                     97
% 23.57/3.50  sim_bw_demodulated:                     124
% 23.57/3.50  sim_light_normalised:                   2181
% 23.57/3.50  sim_joinable_taut:                      0
% 23.57/3.50  sim_joinable_simp:                      0
% 23.57/3.50  sim_ac_normalised:                      0
% 23.57/3.50  sim_smt_subsumption:                    0
% 23.57/3.50  
%------------------------------------------------------------------------------
