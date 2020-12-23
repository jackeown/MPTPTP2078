%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 230 expanded)
%              Number of leaves         :   10 (  65 expanded)
%              Depth                    :   33
%              Number of atoms          :  429 (1343 expanded)
%              Number of equality atoms :   43 (  43 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f38,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_lattices(X0,X1,k6_lattices(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_lattices(sK0,X1,k6_lattices(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r3_lattices(sK0,X1,k6_lattices(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattices)).

fof(f102,plain,(
    ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f36,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f99,f43])).

% (20983)Refutation not found, incomplete strategy% (20983)------------------------------
% (20983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20983)Termination reason: Refutation not found, incomplete strategy

% (20983)Memory used [KB]: 10618
% (20983)Time elapsed: 0.051 s
% (20983)------------------------------
% (20983)------------------------------
fof(f43,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f99,plain,(
    ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,
    ( ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,
    ( ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f96,plain,
    ( ~ v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f95,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f93,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f92,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,
    ( ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f90,f38])).

fof(f90,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f89,plain,
    ( ~ l2_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f88,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f86,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f85,f37])).

fof(f37,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f84,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v14_lattices(sK0) ),
    inference(resolution,[],[f82,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_lattices(X0,X1,k6_lattices(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ v14_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f70,f46])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_lattices(X0,X1,k6_lattices(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ v14_lattices(X0) ) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) != k6_lattices(X0)
      | r1_lattices(X0,X1,k6_lattices(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ v14_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) != k6_lattices(X0)
      | r1_lattices(X0,X1,k6_lattices(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f55,f46])).

fof(f55,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f82,plain,
    ( ~ r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,
    ( ~ r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f80,plain,
    ( ~ r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( ~ r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    ~ r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (20996)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (21001)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (20983)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (21001)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (20996)Refutation not found, incomplete strategy% (20996)------------------------------
% 0.21/0.46  % (20996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f102,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    l3_lattices(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    (~r3_lattices(sK0,sK1,k6_lattices(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r3_lattices(X0,X1,k6_lattices(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r3_lattices(sK0,X1,k6_lattices(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ? [X1] : (~r3_lattices(sK0,X1,k6_lattices(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => (~r3_lattices(sK0,sK1,k6_lattices(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r3_lattices(X0,X1,k6_lattices(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r3_lattices(X0,X1,k6_lattices(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,X1,k6_lattices(X0))))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,X1,k6_lattices(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattices)).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ~l3_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f101,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f100,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v10_lattices(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(resolution,[],[f99,f43])).
% 0.21/0.46  % (20983)Refutation not found, incomplete strategy% (20983)------------------------------
% 0.21/0.46  % (20983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (20983)Memory used [KB]: 10618
% 0.21/0.46  % (20983)Time elapsed: 0.051 s
% 0.21/0.46  % (20983)------------------------------
% 0.21/0.46  % (20983)------------------------------
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    ~v6_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f98,f38])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ~v6_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f97,f35])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~v6_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f96,f36])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ~v6_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(resolution,[],[f95,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ~v8_lattices(sK0) | ~v6_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f94,f38])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f93,f35])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ~v6_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f92,f36])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(resolution,[],[f91,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ~v9_lattices(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f90,f38])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.46    inference(resolution,[],[f89,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~l2_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v9_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f88,f35])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~l2_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f86,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~l2_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f85,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    v14_lattices(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~l2_lattices(sK0) | ~v14_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f84,f35])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~v14_lattices(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f83,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~v14_lattices(sK0)),
% 0.21/0.46    inference(resolution,[],[f82,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_lattices(X0,X1,k6_lattices(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~v14_lattices(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f70,f46])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_lattices(X0,X1,k6_lattices(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~v14_lattices(X0)) )),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_lattices(X0) != k6_lattices(X0) | r1_lattices(X0,X1,k6_lattices(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~v14_lattices(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_lattices(X0) != k6_lattices(X0) | r1_lattices(X0,X1,k6_lattices(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(superposition,[],[f52,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X3] : (k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f46])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X3] : (k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (k1_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ((k1_lattices(X0,sK2(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k1_lattices(X0,sK2(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(rectify,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f35])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f38])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f77,f39])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f54,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~r3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (21001)------------------------------
% 0.21/0.47  % (21001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21001)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (21001)Memory used [KB]: 1663
% 0.21/0.47  % (21001)Time elapsed: 0.059 s
% 0.21/0.47  % (21001)------------------------------
% 0.21/0.47  % (21001)------------------------------
% 0.21/0.47  % (20981)Success in time 0.113 s
%------------------------------------------------------------------------------
