%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:49 EST 2020

% Result     : Theorem 10.82s
% Output     : Refutation 11.22s
% Verified   : 
% Statistics : Number of formulae       :  256 (2403 expanded)
%              Number of leaves         :   30 ( 575 expanded)
%              Depth                    :   30
%              Number of atoms          : 1413 (18670 expanded)
%              Number of equality atoms :  193 (2090 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30369,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30365,f29447])).

fof(f29447,plain,(
    ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f29446,f430])).

fof(f430,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f429,f93])).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f429,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f428,f94])).

fof(f94,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f428,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f96])).

fof(f96,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f29446,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f29442,f391])).

fof(f391,plain,(
    ! [X30] : m1_subset_1(k15_lattice3(sK0,X30),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f336,f93])).

fof(f336,plain,(
    ! [X30] :
      ( m1_subset_1(k15_lattice3(sK0,X30),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f29442,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    inference(resolution,[],[f29269,f3407])).

fof(f3407,plain,(
    ! [X6] :
      ( ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | k5_lattices(sK0) = X6 ) ),
    inference(subsumption_resolution,[],[f3406,f93])).

fof(f3406,plain,(
    ! [X6] :
      ( k5_lattices(sK0) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3405,f352])).

fof(f352,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f351,f93])).

fof(f351,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f318,f94])).

fof(f318,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f3405,plain,(
    ! [X6] :
      ( k5_lattices(sK0) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3404,f354])).

fof(f354,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f353,f93])).

fof(f353,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f319,f94])).

fof(f319,plain,
    ( v9_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3404,plain,(
    ! [X6] :
      ( k5_lattices(sK0) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3403,f96])).

fof(f3403,plain,(
    ! [X6] :
      ( k5_lattices(sK0) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3389,f445])).

fof(f445,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f431,f93])).

fof(f431,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f316,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f316,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f96,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f3389,plain,(
    ! [X6] :
      ( k5_lattices(sK0) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3368])).

fof(f3368,plain,(
    ! [X6] :
      ( k5_lattices(sK0) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X6,k5_lattices(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f3307,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f3307,plain,(
    ! [X55] :
      ( k5_lattices(sK0) = k2_lattices(sK0,X55,k5_lattices(sK0))
      | ~ m1_subset_1(X55,u1_struct_0(sK0))
      | ~ v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f3306,f316])).

fof(f3306,plain,(
    ! [X55] :
      ( k5_lattices(sK0) = k2_lattices(sK0,X55,k5_lattices(sK0))
      | ~ m1_subset_1(X55,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f445])).

fof(f194,plain,(
    ! [X55] :
      ( k5_lattices(sK0) = k2_lattices(sK0,X55,k5_lattices(sK0))
      | ~ m1_subset_1(X55,u1_struct_0(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(resolution,[],[f93,f148])).

fof(f148,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f29269,plain,(
    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(resolution,[],[f8487,f7454])).

fof(f7454,plain,(
    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f7453,f93])).

fof(f7453,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f7452,f94])).

fof(f7452,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f7451,f95])).

fof(f95,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f7451,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f7450,f96])).

fof(f7450,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f7449,f391])).

fof(f7449,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f7440,f445])).

fof(f7440,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f7356,f152])).

fof(f152,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,X2,sK9(X0,X1,X2))
            & sK9(X0,X1,X2) = X0
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f85,f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,sK9(X0,X1,X2))
        & sK9(X0,X1,X2) = X0
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(f7356,plain,(
    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(superposition,[],[f7317,f550])).

fof(f550,plain,(
    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    inference(subsumption_resolution,[],[f549,f93])).

fof(f549,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f548,f94])).

fof(f548,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f547,f95])).

fof(f547,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f490,f96])).

fof(f490,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f445,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f7317,plain,(
    ! [X2] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2)) ),
    inference(resolution,[],[f921,f3935])).

fof(f3935,plain,(
    ! [X0] : ~ r2_hidden(X0,a_2_5_lattice3(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f1083,f98])).

fof(f98,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1083,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,sK11(X4,sK0,X5))
      | ~ r2_hidden(X4,a_2_5_lattice3(sK0,X5)) ) ),
    inference(resolution,[],[f415,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f415,plain,(
    ! [X45,X46] :
      ( r2_hidden(sK11(X45,sK0,X46),X46)
      | ~ r2_hidden(X45,a_2_5_lattice3(sK0,X46)) ) ),
    inference(subsumption_resolution,[],[f414,f93])).

fof(f414,plain,(
    ! [X45,X46] :
      ( r2_hidden(sK11(X45,sK0,X46),X46)
      | ~ r2_hidden(X45,a_2_5_lattice3(sK0,X46))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f413,f94])).

fof(f413,plain,(
    ! [X45,X46] :
      ( r2_hidden(sK11(X45,sK0,X46),X46)
      | ~ r2_hidden(X45,a_2_5_lattice3(sK0,X46))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f344,f95])).

fof(f344,plain,(
    ! [X45,X46] :
      ( r2_hidden(sK11(X45,sK0,X46),X46)
      | ~ r2_hidden(X45,a_2_5_lattice3(sK0,X46))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X2)
            & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2))
            & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
            & sK10(X0,X1,X2) = X0
            & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f89,f91,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,sK10(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK10(X0,X1,X2) = X0
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,sK10(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK11(X0,X1,X2),X2)
        & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2))
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(f921,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6))
      | r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f920,f93])).

fof(f920,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f919,f94])).

fof(f919,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f918,f95])).

fof(f918,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f905,f96])).

fof(f905,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f130,f359])).

fof(f359,plain,(
    ! [X4] : k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4)) ),
    inference(subsumption_resolution,[],[f358,f93])).

fof(f358,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f357,f94])).

fof(f357,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f322,f95])).

fof(f322,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK7(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK7(X0,X1,X2),X1)
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X2)
            | ~ r3_lattices(X0,sK7(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f8487,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X3)))
      | r1_lattices(sK0,k15_lattice3(sK0,X3),X2) ) ),
    inference(subsumption_resolution,[],[f8486,f5353])).

fof(f5353,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f5348])).

fof(f5348,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) ) ),
    inference(superposition,[],[f725,f729])).

fof(f729,plain,(
    ! [X43,X44] :
      ( sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43
      | ~ r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44))) ) ),
    inference(subsumption_resolution,[],[f728,f93])).

fof(f728,plain,(
    ! [X43,X44] :
      ( sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43
      | ~ r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f727,f94])).

fof(f727,plain,(
    ! [X43,X44] :
      ( sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43
      | ~ r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44)))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f726,f95])).

fof(f726,plain,(
    ! [X43,X44] :
      ( sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43
      | ~ r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44)))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f643,f96])).

fof(f643,plain,(
    ! [X43,X44] :
      ( sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43
      | ~ r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44)))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f391,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f725,plain,(
    ! [X41,X42] :
      ( m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0))
      | ~ r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42))) ) ),
    inference(subsumption_resolution,[],[f724,f93])).

fof(f724,plain,(
    ! [X41,X42] :
      ( m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0))
      | ~ r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f723,f94])).

fof(f723,plain,(
    ! [X41,X42] :
      ( m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0))
      | ~ r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42)))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f722,f95])).

fof(f722,plain,(
    ! [X41,X42] :
      ( m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0))
      | ~ r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42)))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f642,f96])).

fof(f642,plain,(
    ! [X41,X42] :
      ( m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0))
      | ~ r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42)))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f391,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f8486,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X3)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X3),X2) ) ),
    inference(subsumption_resolution,[],[f8469,f391])).

fof(f8469,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X3)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X3),X2)
      | ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f713,f1065])).

fof(f1065,plain,(
    ! [X11] :
      ( r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1064,f93])).

fof(f1064,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1063,f94])).

fof(f1063,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1062,f95])).

fof(f1062,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1027,f96])).

fof(f1027,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1024])).

fof(f1024,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f151,f368])).

fof(f368,plain,(
    ! [X7] :
      ( k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f367,f93])).

fof(f367,plain,(
    ! [X7] :
      ( k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f366,f94])).

fof(f366,plain,(
    ! [X7] :
      ( k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f325,f95])).

fof(f325,plain,(
    ! [X7] :
      ( k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f151,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK6(X0,X1,X2),X2)
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f713,plain,(
    ! [X30,X31,X29] :
      ( ~ r3_lattice3(sK0,k15_lattice3(sK0,X29),X31)
      | ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X29),X30) ) ),
    inference(subsumption_resolution,[],[f712,f93])).

fof(f712,plain,(
    ! [X30,X31,X29] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X29),X30)
      | ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,k15_lattice3(sK0,X29),X31)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f637,f96])).

fof(f637,plain,(
    ! [X30,X31,X29] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X29),X30)
      | ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,k15_lattice3(sK0,X29),X31)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f391,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
                  & r2_hidden(sK8(X0,X1,X2),X2)
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f81,f82])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f30365,plain,(
    v13_lattices(sK0) ),
    inference(resolution,[],[f30323,f679])).

fof(f679,plain,(
    ! [X12] :
      ( m1_subset_1(sK2(sK0,k15_lattice3(sK0,X12)),u1_struct_0(sK0))
      | v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f678,f93])).

fof(f678,plain,(
    ! [X12] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X12)),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f627,f316])).

fof(f627,plain,(
    ! [X12] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X12)),u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f391,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f30323,plain,(
    ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f30313,f29447])).

fof(f30313,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | v13_lattices(sK0) ),
    inference(resolution,[],[f29265,f9463])).

fof(f9463,plain,(
    ! [X24] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24)))
      | v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f9462,f679])).

fof(f9462,plain,(
    ! [X24] :
      ( v13_lattices(sK0)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24)))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X24)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f9438,f391])).

fof(f9438,plain,(
    ! [X24] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(k15_lattice3(sK0,X24),u1_struct_0(sK0))
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24)))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X24)),u1_struct_0(sK0)) ) ),
    inference(trivial_inequality_removal,[],[f9419])).

fof(f9419,plain,(
    ! [X24] :
      ( k15_lattice3(sK0,X24) != k15_lattice3(sK0,X24)
      | v13_lattices(sK0)
      | ~ m1_subset_1(k15_lattice3(sK0,X24),u1_struct_0(sK0))
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24)))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X24)),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f3248,f657])).

fof(f657,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f656,f93])).

fof(f656,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f655,f352])).

fof(f655,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f654,f354])).

fof(f654,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f619,f96])).

fof(f619,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f391,f104])).

fof(f3248,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3247,f1405])).

fof(f1405,plain,(
    ! [X8] :
      ( m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f165,f316])).

fof(f165,plain,(
    ! [X8] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l1_lattices(sK0) ) ),
    inference(resolution,[],[f93,f114])).

fof(f3247,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3246,f93])).

fof(f3246,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3204,f316])).

fof(f3204,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f3177])).

fof(f3177,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f115,f3148])).

fof(f3148,plain,(
    ! [X10,X11] :
      ( k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3147,f316])).

fof(f3147,plain,(
    ! [X10,X11] :
      ( k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f350])).

fof(f350,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f349,f93])).

fof(f349,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f317,f94])).

fof(f317,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f167,plain,(
    ! [X10,X11] :
      ( k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(resolution,[],[f93,f116])).

fof(f116,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f69,f71,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f115,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f29265,plain,(
    ! [X2] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f8487,f10886])).

fof(f10886,plain,(
    ! [X5] :
      ( r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f10885,f93])).

fof(f10885,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f10884,f94])).

fof(f10884,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f10883,f95])).

fof(f10883,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f10882,f96])).

fof(f10882,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f10871,f391])).

fof(f10871,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f10870])).

fof(f10870,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f7399,f152])).

fof(f7399,plain,(
    ! [X47] :
      ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X47)
      | ~ m1_subset_1(X47,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f7395,f359])).

fof(f7395,plain,(
    ! [X47] :
      ( r3_lattices(sK0,k15_lattice3(sK0,a_2_5_lattice3(sK0,k1_xboole_0)),X47)
      | ~ m1_subset_1(X47,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1007,f3935])).

fof(f1007,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9)
      | r3_lattices(sK0,k15_lattice3(sK0,X9),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1006,f93])).

fof(f1006,plain,(
    ! [X8,X9] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X9),X8)
      | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1005,f94])).

fof(f1005,plain,(
    ! [X8,X9] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X9),X8)
      | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1004,f95])).

fof(f1004,plain,(
    ! [X8,X9] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X9),X8)
      | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f988,f96])).

fof(f988,plain,(
    ! [X8,X9] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X9),X8)
      | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f130,f365])).

fof(f365,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f364,f93])).

fof(f364,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f363,f94])).

fof(f363,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f324,f95])).

fof(f324,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:21:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (12057)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (12057)Refutation not found, incomplete strategy% (12057)------------------------------
% 0.22/0.53  % (12057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12057)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12057)Memory used [KB]: 10618
% 0.22/0.53  % (12057)Time elapsed: 0.091 s
% 0.22/0.53  % (12057)------------------------------
% 0.22/0.53  % (12057)------------------------------
% 0.22/0.53  % (12065)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.26/0.55  % (12062)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.26/0.56  % (12061)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.62/0.56  % (12053)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.62/0.56  % (12062)Refutation not found, incomplete strategy% (12062)------------------------------
% 1.62/0.56  % (12062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.56  % (12062)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.56  
% 1.62/0.56  % (12062)Memory used [KB]: 10490
% 1.62/0.56  % (12062)Time elapsed: 0.003 s
% 1.62/0.56  % (12062)------------------------------
% 1.62/0.56  % (12062)------------------------------
% 1.62/0.57  % (12052)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.62/0.57  % (12070)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.62/0.58  % (12054)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.62/0.58  % (12069)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.62/0.58  % (12060)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.62/0.58  % (12056)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.62/0.58  % (12051)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.62/0.59  % (12051)Refutation not found, incomplete strategy% (12051)------------------------------
% 1.62/0.59  % (12051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (12051)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (12051)Memory used [KB]: 10490
% 1.62/0.59  % (12051)Time elapsed: 0.002 s
% 1.62/0.59  % (12051)------------------------------
% 1.62/0.59  % (12051)------------------------------
% 1.62/0.59  % (12068)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.62/0.59  % (12055)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.62/0.59  % (12059)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.62/0.60  % (12074)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.62/0.60  % (12066)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.62/0.60  % (12067)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.62/0.61  % (12071)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.62/0.61  % (12058)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.62/0.62  % (12072)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.62/0.62  % (12064)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.62/0.62  % (12075)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.62/0.62  % (12064)Refutation not found, incomplete strategy% (12064)------------------------------
% 1.62/0.62  % (12064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (12064)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.62  
% 1.62/0.62  % (12064)Memory used [KB]: 6140
% 1.62/0.62  % (12064)Time elapsed: 0.187 s
% 1.62/0.62  % (12064)------------------------------
% 1.62/0.62  % (12064)------------------------------
% 1.62/0.62  % (12063)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.62/0.63  % (12073)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.62/0.64  % (12076)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.64/0.71  % (12060)Refutation not found, incomplete strategy% (12060)------------------------------
% 2.64/0.71  % (12060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.71  % (12060)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.71  
% 2.64/0.71  % (12060)Memory used [KB]: 6140
% 2.64/0.71  % (12060)Time elapsed: 0.267 s
% 2.64/0.71  % (12060)------------------------------
% 2.64/0.71  % (12060)------------------------------
% 3.95/0.95  % (12065)Time limit reached!
% 3.95/0.95  % (12065)------------------------------
% 3.95/0.95  % (12065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.95  % (12065)Termination reason: Time limit
% 3.95/0.95  % (12065)Termination phase: Saturation
% 3.95/0.95  
% 3.95/0.95  % (12065)Memory used [KB]: 8443
% 3.95/0.95  % (12065)Time elapsed: 0.500 s
% 3.95/0.95  % (12065)------------------------------
% 3.95/0.95  % (12065)------------------------------
% 7.71/1.35  % (12059)Time limit reached!
% 7.71/1.35  % (12059)------------------------------
% 7.71/1.35  % (12059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.71/1.35  % (12059)Termination reason: Time limit
% 7.71/1.35  % (12059)Termination phase: Saturation
% 7.71/1.35  
% 7.71/1.35  % (12059)Memory used [KB]: 6780
% 7.71/1.35  % (12059)Time elapsed: 0.900 s
% 7.71/1.35  % (12059)------------------------------
% 7.71/1.35  % (12059)------------------------------
% 8.35/1.43  % (12052)Time limit reached!
% 8.35/1.43  % (12052)------------------------------
% 8.35/1.43  % (12052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.35/1.45  % (12052)Termination reason: Time limit
% 8.35/1.45  % (12052)Termination phase: Saturation
% 8.35/1.45  
% 8.35/1.45  % (12052)Memory used [KB]: 20852
% 8.35/1.45  % (12052)Time elapsed: 1.0000 s
% 8.35/1.45  % (12052)------------------------------
% 8.35/1.45  % (12052)------------------------------
% 8.82/1.54  % (12055)Time limit reached!
% 8.82/1.54  % (12055)------------------------------
% 8.82/1.54  % (12055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.82/1.54  % (12055)Termination reason: Time limit
% 8.82/1.54  % (12055)Termination phase: Saturation
% 8.82/1.54  
% 8.82/1.54  % (12055)Memory used [KB]: 10874
% 8.82/1.54  % (12055)Time elapsed: 1.100 s
% 8.82/1.54  % (12055)------------------------------
% 8.82/1.54  % (12055)------------------------------
% 10.82/1.76  % (12069)Refutation found. Thanks to Tanya!
% 10.82/1.76  % SZS status Theorem for theBenchmark
% 11.22/1.78  % SZS output start Proof for theBenchmark
% 11.22/1.78  fof(f30369,plain,(
% 11.22/1.78    $false),
% 11.22/1.78    inference(subsumption_resolution,[],[f30365,f29447])).
% 11.22/1.78  fof(f29447,plain,(
% 11.22/1.78    ~v13_lattices(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f29446,f430])).
% 11.22/1.78  fof(f430,plain,(
% 11.22/1.78    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f429,f93])).
% 11.22/1.78  fof(f93,plain,(
% 11.22/1.78    ~v2_struct_0(sK0)),
% 11.22/1.78    inference(cnf_transformation,[],[f57])).
% 11.22/1.78  fof(f57,plain,(
% 11.22/1.78    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f56])).
% 11.22/1.78  fof(f56,plain,(
% 11.22/1.78    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f25,plain,(
% 11.22/1.78    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f24])).
% 11.22/1.78  fof(f24,plain,(
% 11.22/1.78    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f19])).
% 11.22/1.78  fof(f19,negated_conjecture,(
% 11.22/1.78    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.22/1.78    inference(negated_conjecture,[],[f18])).
% 11.22/1.78  fof(f18,conjecture,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 11.22/1.78  fof(f429,plain,(
% 11.22/1.78    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f428,f94])).
% 11.22/1.78  fof(f94,plain,(
% 11.22/1.78    v10_lattices(sK0)),
% 11.22/1.78    inference(cnf_transformation,[],[f57])).
% 11.22/1.78  fof(f428,plain,(
% 11.22/1.78    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f97,f96])).
% 11.22/1.78  fof(f96,plain,(
% 11.22/1.78    l3_lattices(sK0)),
% 11.22/1.78    inference(cnf_transformation,[],[f57])).
% 11.22/1.78  fof(f97,plain,(
% 11.22/1.78    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(cnf_transformation,[],[f57])).
% 11.22/1.78  fof(f29446,plain,(
% 11.22/1.78    ~v13_lattices(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f29442,f391])).
% 11.22/1.78  fof(f391,plain,(
% 11.22/1.78    ( ! [X30] : (m1_subset_1(k15_lattice3(sK0,X30),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f336,f93])).
% 11.22/1.78  fof(f336,plain,(
% 11.22/1.78    ( ! [X30] : (m1_subset_1(k15_lattice3(sK0,X30),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f96,f136])).
% 11.22/1.78  fof(f136,plain,(
% 11.22/1.78    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f50])).
% 11.22/1.78  fof(f50,plain,(
% 11.22/1.78    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f49])).
% 11.22/1.78  fof(f49,plain,(
% 11.22/1.78    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f11])).
% 11.22/1.78  fof(f11,axiom,(
% 11.22/1.78    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 11.22/1.78  fof(f29442,plain,(
% 11.22/1.78    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 11.22/1.78    inference(resolution,[],[f29269,f3407])).
% 11.22/1.78  fof(f3407,plain,(
% 11.22/1.78    ( ! [X6] : (~r1_lattices(sK0,X6,k5_lattices(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | k5_lattices(sK0) = X6) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3406,f93])).
% 11.22/1.78  fof(f3406,plain,(
% 11.22/1.78    ( ! [X6] : (k5_lattices(sK0) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~r1_lattices(sK0,X6,k5_lattices(sK0)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3405,f352])).
% 11.22/1.78  fof(f352,plain,(
% 11.22/1.78    v8_lattices(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f351,f93])).
% 11.22/1.78  fof(f351,plain,(
% 11.22/1.78    v8_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f318,f94])).
% 11.22/1.78  fof(f318,plain,(
% 11.22/1.78    v8_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(resolution,[],[f96,f102])).
% 11.22/1.78  fof(f102,plain,(
% 11.22/1.78    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f28])).
% 11.22/1.78  fof(f28,plain,(
% 11.22/1.78    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 11.22/1.78    inference(flattening,[],[f27])).
% 11.22/1.78  fof(f27,plain,(
% 11.22/1.78    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 11.22/1.78    inference(ennf_transformation,[],[f23])).
% 11.22/1.78  fof(f23,plain,(
% 11.22/1.78    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 11.22/1.78    inference(pure_predicate_removal,[],[f22])).
% 11.22/1.78  fof(f22,plain,(
% 11.22/1.78    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.22/1.78    inference(pure_predicate_removal,[],[f21])).
% 11.22/1.78  fof(f21,plain,(
% 11.22/1.78    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.22/1.78    inference(pure_predicate_removal,[],[f3])).
% 11.22/1.78  fof(f3,axiom,(
% 11.22/1.78    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 11.22/1.78  fof(f3405,plain,(
% 11.22/1.78    ( ! [X6] : (k5_lattices(sK0) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~r1_lattices(sK0,X6,k5_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3404,f354])).
% 11.22/1.78  fof(f354,plain,(
% 11.22/1.78    v9_lattices(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f353,f93])).
% 11.22/1.78  fof(f353,plain,(
% 11.22/1.78    v9_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f319,f94])).
% 11.22/1.78  fof(f319,plain,(
% 11.22/1.78    v9_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(resolution,[],[f96,f103])).
% 11.22/1.78  fof(f103,plain,(
% 11.22/1.78    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f28])).
% 11.22/1.78  fof(f3404,plain,(
% 11.22/1.78    ( ! [X6] : (k5_lattices(sK0) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~r1_lattices(sK0,X6,k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3403,f96])).
% 11.22/1.78  fof(f3403,plain,(
% 11.22/1.78    ( ! [X6] : (k5_lattices(sK0) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~r1_lattices(sK0,X6,k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3389,f445])).
% 11.22/1.78  fof(f445,plain,(
% 11.22/1.78    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 11.22/1.78    inference(subsumption_resolution,[],[f431,f93])).
% 11.22/1.78  fof(f431,plain,(
% 11.22/1.78    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 11.22/1.78    inference(resolution,[],[f316,f106])).
% 11.22/1.78  fof(f106,plain,(
% 11.22/1.78    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f32])).
% 11.22/1.78  fof(f32,plain,(
% 11.22/1.78    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f31])).
% 11.22/1.78  fof(f31,plain,(
% 11.22/1.78    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f5])).
% 11.22/1.78  fof(f5,axiom,(
% 11.22/1.78    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 11.22/1.78  fof(f316,plain,(
% 11.22/1.78    l1_lattices(sK0)),
% 11.22/1.78    inference(resolution,[],[f96,f99])).
% 11.22/1.78  fof(f99,plain,(
% 11.22/1.78    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f26])).
% 11.22/1.78  fof(f26,plain,(
% 11.22/1.78    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 11.22/1.78    inference(ennf_transformation,[],[f20])).
% 11.22/1.78  fof(f20,plain,(
% 11.22/1.78    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 11.22/1.78    inference(pure_predicate_removal,[],[f6])).
% 11.22/1.78  fof(f6,axiom,(
% 11.22/1.78    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 11.22/1.78  fof(f3389,plain,(
% 11.22/1.78    ( ! [X6] : (k5_lattices(sK0) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~r1_lattices(sK0,X6,k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(duplicate_literal_removal,[],[f3368])).
% 11.22/1.78  fof(f3368,plain,(
% 11.22/1.78    ( ! [X6] : (k5_lattices(sK0) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~r1_lattices(sK0,X6,k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(superposition,[],[f3307,f104])).
% 11.22/1.78  fof(f104,plain,(
% 11.22/1.78    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f58])).
% 11.22/1.78  fof(f58,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(nnf_transformation,[],[f30])).
% 11.22/1.78  fof(f30,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f29])).
% 11.22/1.78  fof(f29,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f7])).
% 11.22/1.78  fof(f7,axiom,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 11.22/1.78  fof(f3307,plain,(
% 11.22/1.78    ( ! [X55] : (k5_lattices(sK0) = k2_lattices(sK0,X55,k5_lattices(sK0)) | ~m1_subset_1(X55,u1_struct_0(sK0)) | ~v13_lattices(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3306,f316])).
% 11.22/1.78  fof(f3306,plain,(
% 11.22/1.78    ( ! [X55] : (k5_lattices(sK0) = k2_lattices(sK0,X55,k5_lattices(sK0)) | ~m1_subset_1(X55,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f194,f445])).
% 11.22/1.78  fof(f194,plain,(
% 11.22/1.78    ( ! [X55] : (k5_lattices(sK0) = k2_lattices(sK0,X55,k5_lattices(sK0)) | ~m1_subset_1(X55,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f93,f148])).
% 11.22/1.78  fof(f148,plain,(
% 11.22/1.78    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(equality_resolution,[],[f108])).
% 11.22/1.78  fof(f108,plain,(
% 11.22/1.78    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f62])).
% 11.22/1.78  fof(f62,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).
% 11.22/1.78  fof(f61,plain,(
% 11.22/1.78    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f60,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(rectify,[],[f59])).
% 11.22/1.78  fof(f59,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(nnf_transformation,[],[f34])).
% 11.22/1.78  fof(f34,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f33])).
% 11.22/1.78  fof(f33,plain,(
% 11.22/1.78    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f4])).
% 11.22/1.78  fof(f4,axiom,(
% 11.22/1.78    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 11.22/1.78  fof(f29269,plain,(
% 11.22/1.78    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 11.22/1.78    inference(resolution,[],[f8487,f7454])).
% 11.22/1.78  fof(f7454,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))),
% 11.22/1.78    inference(subsumption_resolution,[],[f7453,f93])).
% 11.22/1.78  fof(f7453,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f7452,f94])).
% 11.22/1.78  fof(f7452,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f7451,f95])).
% 11.22/1.78  fof(f95,plain,(
% 11.22/1.78    v4_lattice3(sK0)),
% 11.22/1.78    inference(cnf_transformation,[],[f57])).
% 11.22/1.78  fof(f7451,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f7450,f96])).
% 11.22/1.78  fof(f7450,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f7449,f391])).
% 11.22/1.78  fof(f7449,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f7440,f445])).
% 11.22/1.78  fof(f7440,plain,(
% 11.22/1.78    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(resolution,[],[f7356,f152])).
% 11.22/1.78  fof(f152,plain,(
% 11.22/1.78    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_4_lattice3(X1,X2)) | ~r3_lattices(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.22/1.78    inference(equality_resolution,[],[f141])).
% 11.22/1.78  fof(f141,plain,(
% 11.22/1.78    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f87])).
% 11.22/1.78  fof(f87,plain,(
% 11.22/1.78    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattices(X1,X2,sK9(X0,X1,X2)) & sK9(X0,X1,X2) = X0 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f85,f86])).
% 11.22/1.78  fof(f86,plain,(
% 11.22/1.78    ! [X2,X1,X0] : (? [X4] : (r3_lattices(X1,X2,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattices(X1,X2,sK9(X0,X1,X2)) & sK9(X0,X1,X2) = X0 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f85,plain,(
% 11.22/1.78    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,X2,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(rectify,[],[f84])).
% 11.22/1.78  fof(f84,plain,(
% 11.22/1.78    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(nnf_transformation,[],[f53])).
% 11.22/1.78  fof(f53,plain,(
% 11.22/1.78    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(flattening,[],[f52])).
% 11.22/1.78  fof(f52,plain,(
% 11.22/1.78    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 11.22/1.78    inference(ennf_transformation,[],[f12])).
% 11.22/1.78  fof(f12,axiom,(
% 11.22/1.78    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).
% 11.22/1.78  fof(f7356,plain,(
% 11.22/1.78    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 11.22/1.78    inference(superposition,[],[f7317,f550])).
% 11.22/1.78  fof(f550,plain,(
% 11.22/1.78    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 11.22/1.78    inference(subsumption_resolution,[],[f549,f93])).
% 11.22/1.78  fof(f549,plain,(
% 11.22/1.78    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f548,f94])).
% 11.22/1.78  fof(f548,plain,(
% 11.22/1.78    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f547,f95])).
% 11.22/1.78  fof(f547,plain,(
% 11.22/1.78    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f490,f96])).
% 11.22/1.78  fof(f490,plain,(
% 11.22/1.78    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(resolution,[],[f445,f122])).
% 11.22/1.78  fof(f122,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f42])).
% 11.22/1.78  fof(f42,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f41])).
% 11.22/1.78  fof(f41,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f15])).
% 11.22/1.78  fof(f15,axiom,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 11.22/1.78  fof(f7317,plain,(
% 11.22/1.78    ( ! [X2] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))) )),
% 11.22/1.78    inference(resolution,[],[f921,f3935])).
% 11.22/1.78  fof(f3935,plain,(
% 11.22/1.78    ( ! [X0] : (~r2_hidden(X0,a_2_5_lattice3(sK0,k1_xboole_0))) )),
% 11.22/1.78    inference(resolution,[],[f1083,f98])).
% 11.22/1.78  fof(f98,plain,(
% 11.22/1.78    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f1])).
% 11.22/1.78  fof(f1,axiom,(
% 11.22/1.78    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 11.22/1.78  fof(f1083,plain,(
% 11.22/1.78    ( ! [X4,X5] : (~r1_tarski(X5,sK11(X4,sK0,X5)) | ~r2_hidden(X4,a_2_5_lattice3(sK0,X5))) )),
% 11.22/1.78    inference(resolution,[],[f415,f137])).
% 11.22/1.78  fof(f137,plain,(
% 11.22/1.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f51])).
% 11.22/1.78  fof(f51,plain,(
% 11.22/1.78    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.22/1.78    inference(ennf_transformation,[],[f2])).
% 11.22/1.78  fof(f2,axiom,(
% 11.22/1.78    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 11.22/1.78  fof(f415,plain,(
% 11.22/1.78    ( ! [X45,X46] : (r2_hidden(sK11(X45,sK0,X46),X46) | ~r2_hidden(X45,a_2_5_lattice3(sK0,X46))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f414,f93])).
% 11.22/1.78  fof(f414,plain,(
% 11.22/1.78    ( ! [X45,X46] : (r2_hidden(sK11(X45,sK0,X46),X46) | ~r2_hidden(X45,a_2_5_lattice3(sK0,X46)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f413,f94])).
% 11.22/1.78  fof(f413,plain,(
% 11.22/1.78    ( ! [X45,X46] : (r2_hidden(sK11(X45,sK0,X46),X46) | ~r2_hidden(X45,a_2_5_lattice3(sK0,X46)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f344,f95])).
% 11.22/1.78  fof(f344,plain,(
% 11.22/1.78    ( ! [X45,X46] : (r2_hidden(sK11(X45,sK0,X46),X46) | ~r2_hidden(X45,a_2_5_lattice3(sK0,X46)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f96,f146])).
% 11.22/1.78  fof(f146,plain,(
% 11.22/1.78    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f92])).
% 11.22/1.78  fof(f92,plain,(
% 11.22/1.78    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK11(X0,X1,X2),X2) & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2)) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))) & sK10(X0,X1,X2) = X0 & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f89,f91,f90])).
% 11.22/1.78  fof(f90,plain,(
% 11.22/1.78    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK10(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK10(X0,X1,X2) = X0 & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f91,plain,(
% 11.22/1.78    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK10(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK11(X0,X1,X2),X2) & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2)) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f89,plain,(
% 11.22/1.78    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(rectify,[],[f88])).
% 11.22/1.78  fof(f88,plain,(
% 11.22/1.78    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(nnf_transformation,[],[f55])).
% 11.22/1.78  fof(f55,plain,(
% 11.22/1.78    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.22/1.78    inference(flattening,[],[f54])).
% 11.22/1.78  fof(f54,plain,(
% 11.22/1.78    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 11.22/1.78    inference(ennf_transformation,[],[f13])).
% 11.22/1.78  fof(f13,axiom,(
% 11.22/1.78    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 11.22/1.78  fof(f921,plain,(
% 11.22/1.78    ( ! [X6,X7] : (r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6)) | r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f920,f93])).
% 11.22/1.78  fof(f920,plain,(
% 11.22/1.78    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f919,f94])).
% 11.22/1.78  fof(f919,plain,(
% 11.22/1.78    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f918,f95])).
% 11.22/1.78  fof(f918,plain,(
% 11.22/1.78    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f905,f96])).
% 11.22/1.78  fof(f905,plain,(
% 11.22/1.78    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | r2_hidden(sK7(sK0,a_2_5_lattice3(sK0,X6),X7),a_2_5_lattice3(sK0,X6)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(superposition,[],[f130,f359])).
% 11.22/1.78  fof(f359,plain,(
% 11.22/1.78    ( ! [X4] : (k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f358,f93])).
% 11.22/1.78  fof(f358,plain,(
% 11.22/1.78    ( ! [X4] : (k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f357,f94])).
% 11.22/1.78  fof(f357,plain,(
% 11.22/1.78    ( ! [X4] : (k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f322,f95])).
% 11.22/1.78  fof(f322,plain,(
% 11.22/1.78    ( ! [X4] : (k15_lattice3(sK0,X4) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X4)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f96,f120])).
% 11.22/1.78  fof(f120,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f40])).
% 11.22/1.78  fof(f40,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f39])).
% 11.22/1.78  fof(f39,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f16])).
% 11.22/1.78  fof(f16,axiom,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).
% 11.22/1.78  fof(f130,plain,(
% 11.22/1.78    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK7(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f79])).
% 11.22/1.78  fof(f79,plain,(
% 11.22/1.78    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f78])).
% 11.22/1.78  fof(f78,plain,(
% 11.22/1.78    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f46,plain,(
% 11.22/1.78    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f45])).
% 11.22/1.78  fof(f45,plain,(
% 11.22/1.78    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f17])).
% 11.22/1.78  fof(f17,axiom,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 11.22/1.78  fof(f8487,plain,(
% 11.22/1.78    ( ! [X2,X3] : (~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X3))) | r1_lattices(sK0,k15_lattice3(sK0,X3),X2)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f8486,f5353])).
% 11.22/1.78  fof(f5353,plain,(
% 11.22/1.78    ( ! [X0,X1] : (~r2_hidden(X0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(duplicate_literal_removal,[],[f5348])).
% 11.22/1.78  fof(f5348,plain,(
% 11.22/1.78    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~r2_hidden(X0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))) )),
% 11.22/1.78    inference(superposition,[],[f725,f729])).
% 11.22/1.78  fof(f729,plain,(
% 11.22/1.78    ( ! [X43,X44] : (sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43 | ~r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44)))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f728,f93])).
% 11.22/1.78  fof(f728,plain,(
% 11.22/1.78    ( ! [X43,X44] : (sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43 | ~r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44))) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f727,f94])).
% 11.22/1.78  fof(f727,plain,(
% 11.22/1.78    ( ! [X43,X44] : (sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43 | ~r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f726,f95])).
% 11.22/1.78  fof(f726,plain,(
% 11.22/1.78    ( ! [X43,X44] : (sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43 | ~r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f643,f96])).
% 11.22/1.78  fof(f643,plain,(
% 11.22/1.78    ( ! [X43,X44] : (sK9(X43,sK0,k15_lattice3(sK0,X44)) = X43 | ~r2_hidden(X43,a_2_4_lattice3(sK0,k15_lattice3(sK0,X44))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f391,f139])).
% 11.22/1.78  fof(f139,plain,(
% 11.22/1.78    ( ! [X2,X0,X1] : (sK9(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f87])).
% 11.22/1.78  fof(f725,plain,(
% 11.22/1.78    ( ! [X41,X42] : (m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0)) | ~r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42)))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f724,f93])).
% 11.22/1.78  fof(f724,plain,(
% 11.22/1.78    ( ! [X41,X42] : (m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0)) | ~r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42))) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f723,f94])).
% 11.22/1.78  fof(f723,plain,(
% 11.22/1.78    ( ! [X41,X42] : (m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0)) | ~r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f722,f95])).
% 11.22/1.78  fof(f722,plain,(
% 11.22/1.78    ( ! [X41,X42] : (m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0)) | ~r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f642,f96])).
% 11.22/1.78  fof(f642,plain,(
% 11.22/1.78    ( ! [X41,X42] : (m1_subset_1(sK9(X41,sK0,k15_lattice3(sK0,X42)),u1_struct_0(sK0)) | ~r2_hidden(X41,a_2_4_lattice3(sK0,k15_lattice3(sK0,X42))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f391,f138])).
% 11.22/1.78  fof(f138,plain,(
% 11.22/1.78    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f87])).
% 11.22/1.78  fof(f8486,plain,(
% 11.22/1.78    ( ! [X2,X3] : (~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X2)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f8469,f391])).
% 11.22/1.78  fof(f8469,plain,(
% 11.22/1.78    ( ! [X2,X3] : (~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X2) | ~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(resolution,[],[f713,f1065])).
% 11.22/1.78  fof(f1065,plain,(
% 11.22/1.78    ( ! [X11] : (r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11)) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1064,f93])).
% 11.22/1.78  fof(f1064,plain,(
% 11.22/1.78    ( ! [X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1063,f94])).
% 11.22/1.78  fof(f1063,plain,(
% 11.22/1.78    ( ! [X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1062,f95])).
% 11.22/1.78  fof(f1062,plain,(
% 11.22/1.78    ( ! [X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1027,f96])).
% 11.22/1.78  fof(f1027,plain,(
% 11.22/1.78    ( ! [X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(duplicate_literal_removal,[],[f1024])).
% 11.22/1.78  fof(f1024,plain,(
% 11.22/1.78    ( ! [X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | r3_lattice3(sK0,X11,a_2_4_lattice3(sK0,X11)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(superposition,[],[f151,f368])).
% 11.22/1.78  fof(f368,plain,(
% 11.22/1.78    ( ! [X7] : (k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f367,f93])).
% 11.22/1.78  fof(f367,plain,(
% 11.22/1.78    ( ! [X7] : (k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f366,f94])).
% 11.22/1.78  fof(f366,plain,(
% 11.22/1.78    ( ! [X7] : (k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f325,f95])).
% 11.22/1.78  fof(f325,plain,(
% 11.22/1.78    ( ! [X7] : (k16_lattice3(sK0,a_2_4_lattice3(sK0,X7)) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f96,f123])).
% 11.22/1.78  fof(f123,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f42])).
% 11.22/1.78  fof(f151,plain,(
% 11.22/1.78    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(equality_resolution,[],[f124])).
% 11.22/1.78  fof(f124,plain,(
% 11.22/1.78    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f77])).
% 11.22/1.78  fof(f77,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).
% 11.22/1.78  fof(f76,plain,(
% 11.22/1.78    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f75,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(rectify,[],[f74])).
% 11.22/1.78  fof(f74,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f73])).
% 11.22/1.78  fof(f73,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(nnf_transformation,[],[f44])).
% 11.22/1.78  fof(f44,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f43])).
% 11.22/1.78  fof(f43,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f14])).
% 11.22/1.78  fof(f14,axiom,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 11.22/1.78  fof(f713,plain,(
% 11.22/1.78    ( ! [X30,X31,X29] : (~r3_lattice3(sK0,k15_lattice3(sK0,X29),X31) | ~r2_hidden(X30,X31) | ~m1_subset_1(X30,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X29),X30)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f712,f93])).
% 11.22/1.78  fof(f712,plain,(
% 11.22/1.78    ( ! [X30,X31,X29] : (r1_lattices(sK0,k15_lattice3(sK0,X29),X30) | ~r2_hidden(X30,X31) | ~m1_subset_1(X30,u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X29),X31) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f637,f96])).
% 11.22/1.78  fof(f637,plain,(
% 11.22/1.78    ( ! [X30,X31,X29] : (r1_lattices(sK0,k15_lattice3(sK0,X29),X30) | ~r2_hidden(X30,X31) | ~m1_subset_1(X30,u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X29),X31) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f391,f132])).
% 11.22/1.78  fof(f132,plain,(
% 11.22/1.78    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f83])).
% 11.22/1.78  fof(f83,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f81,f82])).
% 11.22/1.78  fof(f82,plain,(
% 11.22/1.78    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f81,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(rectify,[],[f80])).
% 11.22/1.78  fof(f80,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(nnf_transformation,[],[f48])).
% 11.22/1.78  fof(f48,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f47])).
% 11.22/1.78  fof(f47,plain,(
% 11.22/1.78    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f9])).
% 11.22/1.78  fof(f9,axiom,(
% 11.22/1.78    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 11.22/1.78  fof(f30365,plain,(
% 11.22/1.78    v13_lattices(sK0)),
% 11.22/1.78    inference(resolution,[],[f30323,f679])).
% 11.22/1.78  fof(f679,plain,(
% 11.22/1.78    ( ! [X12] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X12)),u1_struct_0(sK0)) | v13_lattices(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f678,f93])).
% 11.22/1.78  fof(f678,plain,(
% 11.22/1.78    ( ! [X12] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X12)),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f627,f316])).
% 11.22/1.78  fof(f627,plain,(
% 11.22/1.78    ( ! [X12] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X12)),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f391,f114])).
% 11.22/1.78  fof(f114,plain,(
% 11.22/1.78    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f67])).
% 11.22/1.78  fof(f67,plain,(
% 11.22/1.78    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f64,f66,f65])).
% 11.22/1.78  fof(f65,plain,(
% 11.22/1.78    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f66,plain,(
% 11.22/1.78    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f64,plain,(
% 11.22/1.78    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(rectify,[],[f63])).
% 11.22/1.78  fof(f63,plain,(
% 11.22/1.78    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(nnf_transformation,[],[f36])).
% 11.22/1.78  fof(f36,plain,(
% 11.22/1.78    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f35])).
% 11.22/1.78  fof(f35,plain,(
% 11.22/1.78    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f8])).
% 11.22/1.78  fof(f8,axiom,(
% 11.22/1.78    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 11.22/1.78  fof(f30323,plain,(
% 11.22/1.78    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 11.22/1.78    inference(subsumption_resolution,[],[f30313,f29447])).
% 11.22/1.78  fof(f30313,plain,(
% 11.22/1.78    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | v13_lattices(sK0)),
% 11.22/1.78    inference(resolution,[],[f29265,f9463])).
% 11.22/1.78  fof(f9463,plain,(
% 11.22/1.78    ( ! [X24] : (~r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24))) | v13_lattices(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f9462,f679])).
% 11.22/1.78  fof(f9462,plain,(
% 11.22/1.78    ( ! [X24] : (v13_lattices(sK0) | ~r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,X24)),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f9438,f391])).
% 11.22/1.78  fof(f9438,plain,(
% 11.22/1.78    ( ! [X24] : (v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X24),u1_struct_0(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,X24)),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(trivial_inequality_removal,[],[f9419])).
% 11.22/1.78  fof(f9419,plain,(
% 11.22/1.78    ( ! [X24] : (k15_lattice3(sK0,X24) != k15_lattice3(sK0,X24) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X24),u1_struct_0(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X24),sK2(sK0,k15_lattice3(sK0,X24))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,X24)),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(superposition,[],[f3248,f657])).
% 11.22/1.78  fof(f657,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f656,f93])).
% 11.22/1.78  fof(f656,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f655,f352])).
% 11.22/1.78  fof(f655,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f654,f354])).
% 11.22/1.78  fof(f654,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f619,f96])).
% 11.22/1.78  fof(f619,plain,(
% 11.22/1.78    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f391,f104])).
% 11.22/1.78  fof(f3248,plain,(
% 11.22/1.78    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3247,f1405])).
% 11.22/1.78  fof(f1405,plain,(
% 11.22/1.78    ( ! [X8] : (m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0)) | v13_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f165,f316])).
% 11.22/1.78  fof(f165,plain,(
% 11.22/1.78    ( ! [X8] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~l1_lattices(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f93,f114])).
% 11.22/1.78  fof(f3247,plain,(
% 11.22/1.78    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3246,f93])).
% 11.22/1.78  fof(f3246,plain,(
% 11.22/1.78    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3204,f316])).
% 11.22/1.78  fof(f3204,plain,(
% 11.22/1.78    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))) )),
% 11.22/1.78    inference(duplicate_literal_removal,[],[f3177])).
% 11.22/1.78  fof(f3177,plain,(
% 11.22/1.78    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(superposition,[],[f115,f3148])).
% 11.22/1.78  fof(f3148,plain,(
% 11.22/1.78    ( ! [X10,X11] : (k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f3147,f316])).
% 11.22/1.78  fof(f3147,plain,(
% 11.22/1.78    ( ! [X10,X11] : (k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~l1_lattices(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f167,f350])).
% 11.22/1.78  fof(f350,plain,(
% 11.22/1.78    v6_lattices(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f349,f93])).
% 11.22/1.78  fof(f349,plain,(
% 11.22/1.78    v6_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(subsumption_resolution,[],[f317,f94])).
% 11.22/1.78  fof(f317,plain,(
% 11.22/1.78    v6_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.22/1.78    inference(resolution,[],[f96,f101])).
% 11.22/1.78  fof(f101,plain,(
% 11.22/1.78    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f28])).
% 11.22/1.78  fof(f167,plain,(
% 11.22/1.78    ( ! [X10,X11] : (k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f93,f116])).
% 11.22/1.78  fof(f116,plain,(
% 11.22/1.78    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f72])).
% 11.22/1.78  fof(f72,plain,(
% 11.22/1.78    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f69,f71,f70])).
% 11.22/1.78  fof(f70,plain,(
% 11.22/1.78    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f71,plain,(
% 11.22/1.78    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 11.22/1.78    introduced(choice_axiom,[])).
% 11.22/1.78  fof(f69,plain,(
% 11.22/1.78    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(rectify,[],[f68])).
% 11.22/1.78  fof(f68,plain,(
% 11.22/1.78    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(nnf_transformation,[],[f38])).
% 11.22/1.78  fof(f38,plain,(
% 11.22/1.78    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.22/1.78    inference(flattening,[],[f37])).
% 11.22/1.78  fof(f37,plain,(
% 11.22/1.78    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.22/1.78    inference(ennf_transformation,[],[f10])).
% 11.22/1.78  fof(f10,axiom,(
% 11.22/1.78    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 11.22/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 11.22/1.78  fof(f115,plain,(
% 11.22/1.78    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.22/1.78    inference(cnf_transformation,[],[f67])).
% 11.22/1.78  fof(f29265,plain,(
% 11.22/1.78    ( ! [X2] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(resolution,[],[f8487,f10886])).
% 11.22/1.78  fof(f10886,plain,(
% 11.22/1.78    ( ! [X5] : (r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f10885,f93])).
% 11.22/1.78  fof(f10885,plain,(
% 11.22/1.78    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f10884,f94])).
% 11.22/1.78  fof(f10884,plain,(
% 11.22/1.78    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f10883,f95])).
% 11.22/1.78  fof(f10883,plain,(
% 11.22/1.78    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f10882,f96])).
% 11.22/1.78  fof(f10882,plain,(
% 11.22/1.78    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f10871,f391])).
% 11.22/1.78  fof(f10871,plain,(
% 11.22/1.78    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(duplicate_literal_removal,[],[f10870])).
% 11.22/1.78  fof(f10870,plain,(
% 11.22/1.78    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f7399,f152])).
% 11.22/1.78  fof(f7399,plain,(
% 11.22/1.78    ( ! [X47] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X47) | ~m1_subset_1(X47,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(forward_demodulation,[],[f7395,f359])).
% 11.22/1.78  fof(f7395,plain,(
% 11.22/1.78    ( ! [X47] : (r3_lattices(sK0,k15_lattice3(sK0,a_2_5_lattice3(sK0,k1_xboole_0)),X47) | ~m1_subset_1(X47,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(resolution,[],[f1007,f3935])).
% 11.22/1.78  fof(f1007,plain,(
% 11.22/1.78    ( ! [X8,X9] : (r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9) | r3_lattices(sK0,k15_lattice3(sK0,X9),X8) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1006,f93])).
% 11.22/1.78  fof(f1006,plain,(
% 11.22/1.78    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),X8) | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9) | v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1005,f94])).
% 11.22/1.78  fof(f1005,plain,(
% 11.22/1.78    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),X8) | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f1004,f95])).
% 11.22/1.78  fof(f1004,plain,(
% 11.22/1.78    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),X8) | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f988,f96])).
% 11.22/1.78  fof(f988,plain,(
% 11.22/1.78    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),X8) | r2_hidden(sK7(sK0,X9,a_2_3_lattice3(sK0,X8)),X9) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(superposition,[],[f130,f365])).
% 11.22/1.78  fof(f365,plain,(
% 11.22/1.78    ( ! [X6] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0))) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f364,f93])).
% 11.22/1.78  fof(f364,plain,(
% 11.22/1.78    ( ! [X6] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f363,f94])).
% 11.22/1.78  fof(f363,plain,(
% 11.22/1.78    ( ! [X6] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(subsumption_resolution,[],[f324,f95])).
% 11.22/1.78  fof(f324,plain,(
% 11.22/1.78    ( ! [X6] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X6)) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 11.22/1.78    inference(resolution,[],[f96,f122])).
% 11.22/1.78  % SZS output end Proof for theBenchmark
% 11.22/1.78  % (12069)------------------------------
% 11.22/1.78  % (12069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.22/1.78  % (12069)Termination reason: Refutation
% 11.22/1.78  
% 11.22/1.78  % (12069)Memory used [KB]: 16247
% 11.22/1.78  % (12069)Time elapsed: 1.337 s
% 11.22/1.78  % (12069)------------------------------
% 11.22/1.78  % (12069)------------------------------
% 11.22/1.78  % (12050)Success in time 1.421 s
%------------------------------------------------------------------------------
