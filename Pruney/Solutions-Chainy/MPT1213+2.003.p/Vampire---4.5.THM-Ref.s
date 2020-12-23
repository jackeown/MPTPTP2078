%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 319 expanded)
%              Number of leaves         :    9 (  90 expanded)
%              Depth                    :   23
%              Number of atoms          :  494 (1969 expanded)
%              Number of equality atoms :   76 ( 401 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f94,f137])).

fof(f137,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f135,f25])).

fof(f25,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

% (13882)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k7_lattices(sK0,k7_lattices(sK0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( k7_lattices(sK0,k7_lattices(sK0,X1)) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f135,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f134,f46])).

fof(f46,plain,(
    v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f27,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( v11_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f44,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,
    ( v11_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f31,f26])).

fof(f26,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f134,plain,
    ( ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f133,f49])).

fof(f49,plain,(
    v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f48,f27])).

fof(f48,plain,
    ( v16_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f47,f24])).

fof(f47,plain,
    ( v16_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f133,plain,
    ( ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f132,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f131,f24])).

fof(f131,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f123,f27])).

fof(f123,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f119,f109])).

fof(f109,plain,
    ( ~ r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f108,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | ~ spl2_2 ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,
    ( ! [X1] :
        ( sK1 != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_2
  <=> ! [X1] :
        ( sK1 != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,X1,k7_lattices(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r2_lattices(X0,X1,k7_lattices(X0,X1))
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r2_lattices(X0,X1,k7_lattices(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f42,f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_lattices(X0,X1) = X2
                  | ~ r2_lattices(X0,X2,X1) )
                & ( r2_lattices(X0,X2,X1)
                  | k7_lattices(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ( l3_lattices(X0)
              & v16_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,X1) = X2
                <=> r2_lattices(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattices)).

fof(f87,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattices(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | r2_lattices(X3,X5,X4) ) ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k6_lattices(X0) = k1_lattices(X0,X2,X1)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k5_lattices(X0) != k2_lattices(X0,X2,X1)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k6_lattices(X0) != k1_lattices(X0,X2,X1)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k5_lattices(X0) != k2_lattices(X0,X2,X1)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k6_lattices(X0) != k1_lattices(X0,X2,X1)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattices)).

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( r2_lattices(X3,X5,X4)
      | k6_lattices(X3) != k1_lattices(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_lattices(X3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f85,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k6_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X4,X5,X3] :
      ( r2_lattices(X3,X5,X4)
      | k1_lattices(X3,X4,X5) != k6_lattices(X3)
      | k6_lattices(X3) != k1_lattices(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_lattices(X3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f83,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X4,X5,X3] :
      ( r2_lattices(X3,X5,X4)
      | k5_lattices(X3) != k2_lattices(X3,X5,X4)
      | k1_lattices(X3,X4,X5) != k6_lattices(X3)
      | k6_lattices(X3) != k1_lattices(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_lattices(X3,X4,X5) ) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,(
    ! [X4,X5,X3] :
      ( k5_lattices(X3) != k5_lattices(X3)
      | r2_lattices(X3,X5,X4)
      | k5_lattices(X3) != k2_lattices(X3,X5,X4)
      | k1_lattices(X3,X4,X5) != k6_lattices(X3)
      | k6_lattices(X3) != k1_lattices(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_lattices(X3,X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X4,X5,X3] :
      ( k5_lattices(X3) != k5_lattices(X3)
      | r2_lattices(X3,X5,X4)
      | k5_lattices(X3) != k2_lattices(X3,X5,X4)
      | k1_lattices(X3,X4,X5) != k6_lattices(X3)
      | k6_lattices(X3) != k1_lattices(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_lattices(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k5_lattices(X0) != k2_lattices(X0,X2,X1)
      | r2_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != k5_lattices(X0)
      | k6_lattices(X0) != k1_lattices(X0,X2,X1)
      | k1_lattices(X0,X1,X2) != k6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f92,f24])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f91,f27])).

fof(f91,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f88,f28])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_1 ),
    inference(resolution,[],[f75,f40])).

fof(f75,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_1
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f79,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f72,f77,f74])).

fof(f72,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f71,f24])).

fof(f71,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f70,f25])).

fof(f70,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f69,f46])).

fof(f69,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f68,f49])).

fof(f68,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v16_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f54,f27])).

fof(f54,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_lattices(sK0,X1,k7_lattices(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f29,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,X1) = X2
      | ~ r2_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,X1) = X2
      | ~ r2_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:56:37 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.47  % (13876)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (13875)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (13876)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (13884)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f79,f94,f137])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ~spl2_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    $false | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f135,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v10_lattices(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    (sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 0.22/0.48  % (13882)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k7_lattices(sK0,k7_lattices(sK0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X1] : (k7_lattices(sK0,k7_lattices(sK0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) => (sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ~v10_lattices(sK0) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f134,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    v11_lattices(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f45,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    l3_lattices(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v11_lattices(sK0) | ~l3_lattices(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f44,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    v11_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.48    inference(resolution,[],[f31,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v17_lattices(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (~v17_lattices(X0) | v11_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : ((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~v11_lattices(sK0) | ~v10_lattices(sK0) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f133,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    v16_lattices(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f48,f27])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    v16_lattices(sK0) | ~l3_lattices(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f24])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v16_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.48    inference(resolution,[],[f32,f26])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (~v17_lattices(X0) | v16_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f131,f24])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f123,f27])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | ~spl2_2),
% 0.22/0.48    inference(resolution,[],[f119,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ~r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f28])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) | ~spl2_2),
% 0.22/0.48    inference(equality_resolution,[],[f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X1] : (sK1 != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1))) ) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl2_2 <=> ! [X1] : (sK1 != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_lattices(X0,X1,k7_lattices(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | r2_lattices(X0,X1,k7_lattices(X0,X1)) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | r2_lattices(X0,X1,k7_lattices(X0,X1)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.48    inference(resolution,[],[f87,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(resolution,[],[f42,f40])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | r2_lattices(X0,k7_lattices(X0,X1),X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1)) & (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ((l3_lattices(X0) & v16_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattices)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r2_lattices(X3,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3) | r2_lattices(X3,X5,X4)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f86,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k6_lattices(X0) = k1_lattices(X0,X2,X1) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | k5_lattices(X0) != k2_lattices(X0,X2,X1) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k6_lattices(X0) != k1_lattices(X0,X2,X1) | k1_lattices(X0,X1,X2) != k6_lattices(X0)) & ((k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | (k5_lattices(X0) != k2_lattices(X0,X2,X1) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k6_lattices(X0) != k1_lattices(X0,X2,X1) | k1_lattices(X0,X1,X2) != k6_lattices(X0))) & ((k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattices(X0,X1,X2) <=> (k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattices)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (r2_lattices(X3,X5,X4) | k6_lattices(X3) != k1_lattices(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3) | ~r2_lattices(X3,X4,X5)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k6_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (r2_lattices(X3,X5,X4) | k1_lattices(X3,X4,X5) != k6_lattices(X3) | k6_lattices(X3) != k1_lattices(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3) | ~r2_lattices(X3,X4,X5)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f83,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_lattices(X0) = k2_lattices(X0,X2,X1) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (r2_lattices(X3,X5,X4) | k5_lattices(X3) != k2_lattices(X3,X5,X4) | k1_lattices(X3,X4,X5) != k6_lattices(X3) | k6_lattices(X3) != k1_lattices(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3) | ~r2_lattices(X3,X4,X5)) )),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k5_lattices(X3) != k5_lattices(X3) | r2_lattices(X3,X5,X4) | k5_lattices(X3) != k2_lattices(X3,X5,X4) | k1_lattices(X3,X4,X5) != k6_lattices(X3) | k6_lattices(X3) != k1_lattices(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3) | ~r2_lattices(X3,X4,X5)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k5_lattices(X3) != k5_lattices(X3) | r2_lattices(X3,X5,X4) | k5_lattices(X3) != k2_lattices(X3,X5,X4) | k1_lattices(X3,X4,X5) != k6_lattices(X3) | k6_lattices(X3) != k1_lattices(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3) | ~r2_lattices(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | v2_struct_0(X3)) )),
% 0.22/0.49    inference(superposition,[],[f39,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k5_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_lattices(X0) != k2_lattices(X0,X2,X1) | r2_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k6_lattices(X0) != k1_lattices(X0,X2,X1) | k1_lattices(X0,X1,X2) != k6_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    $false | spl2_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f24])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    v2_struct_0(sK0) | spl2_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f27])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl2_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f28])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl2_1),
% 0.22/0.49    inference(resolution,[],[f75,f40])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl2_1 <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ~spl2_1 | spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f72,f77,f74])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X1] : (sK1 != X1 | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f71,f24])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X1] : (sK1 != X1 | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f25])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X1] : (sK1 != X1 | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f46])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X1] : (sK1 != X1 | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f49])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X1] : (sK1 != X1 | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f54,f27])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X1] : (sK1 != X1 | ~r2_lattices(sK0,X1,k7_lattices(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(superposition,[],[f29,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (13876)------------------------------
% 0.22/0.49  % (13876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13876)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (13876)Memory used [KB]: 10618
% 0.22/0.49  % (13876)Time elapsed: 0.067 s
% 0.22/0.49  % (13876)------------------------------
% 0.22/0.49  % (13876)------------------------------
% 0.22/0.49  % (13875)Refutation not found, incomplete strategy% (13875)------------------------------
% 0.22/0.49  % (13875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13875)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13875)Memory used [KB]: 10618
% 0.22/0.49  % (13875)Time elapsed: 0.069 s
% 0.22/0.49  % (13875)------------------------------
% 0.22/0.49  % (13875)------------------------------
% 0.22/0.49  % (13873)Success in time 0.122 s
%------------------------------------------------------------------------------
