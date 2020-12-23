%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 292 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          :  537 (1521 expanded)
%              Number of equality atoms :   85 ( 258 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f869,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f161,f196,f264,f276,f320,f326,f724,f868])).

fof(f868,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f867])).

fof(f867,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(subsumption_resolution,[],[f866,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,k6_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK0,k6_lattices(sK0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k4_lattices(sK0,k6_lattices(sK0),X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(f866,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(subsumption_resolution,[],[f865,f80])).

fof(f80,plain,
    ( v6_lattices(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_1
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f865,plain,
    ( ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(subsumption_resolution,[],[f864,f84])).

fof(f84,plain,
    ( l1_lattices(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_2
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f864,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(subsumption_resolution,[],[f863,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f863,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(subsumption_resolution,[],[f862,f140])).

fof(f140,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_15
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f862,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28
    | spl5_32 ),
    inference(subsumption_resolution,[],[f848,f312])).

fof(f312,plain,
    ( sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl5_32
  <=> sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f848,plain,
    ( sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(superposition,[],[f48,f844])).

fof(f844,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f843,f41])).

fof(f843,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f842,f44])).

fof(f44,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f842,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f841,f100])).

fof(f100,plain,
    ( v9_lattices(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_6
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f841,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f840,f45])).

fof(f840,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_15
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f833,f140])).

fof(f833,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_28 ),
    inference(superposition,[],[f49,f263])).

fof(f263,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_28
  <=> k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f49,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (3222)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f724,plain,
    ( ~ spl5_15
    | ~ spl5_32
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f723,f83,f79,f310,f138])).

fof(f723,plain,
    ( sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f722,f41])).

fof(f722,plain,
    ( sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f721,f80])).

fof(f721,plain,
    ( sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f720,f84])).

fof(f720,plain,
    ( sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f708,f45])).

fof(f708,plain,
    ( sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f46,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f46,plain,(
    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f326,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f324,f44])).

fof(f324,plain,
    ( ~ l3_lattices(sK0)
    | spl5_11 ),
    inference(resolution,[],[f124,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f124,plain,
    ( ~ l2_lattices(sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_11
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f320,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f97,plain,
    ( ~ l3_lattices(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_5
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f276,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f274,f44])).

fof(f274,plain,
    ( ~ l3_lattices(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f273,f41])).

fof(f273,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f272,f42])).

fof(f42,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f272,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl5_1 ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

% (3231)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
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

fof(f81,plain,
    ( ~ v6_lattices(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f264,plain,
    ( ~ spl5_11
    | ~ spl5_15
    | spl5_28 ),
    inference(avatar_split_clause,[],[f259,f261,f138,f122])).

fof(f259,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f258,f41])).

fof(f258,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f43])).

fof(f43,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f205,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK4(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK4(X0,X1)) != X1 )
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK4(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK4(X0,X1)) != X1 )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f196,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f194,f44])).

fof(f194,plain,
    ( ~ l3_lattices(sK0)
    | spl5_2 ),
    inference(resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( ~ l1_lattices(sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f161,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f160,f99,f95])).

fof(f160,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f157,f41])).

fof(f157,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f42,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,
    ( ~ spl5_11
    | spl5_15 ),
    inference(avatar_split_clause,[],[f73,f138,f122])).

fof(f73,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3237)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.47  % (3226)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (3219)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (3237)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (3230)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f869,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f141,f161,f196,f264,f276,f320,f326,f724,f868])).
% 0.22/0.49  fof(f868,plain,(
% 0.22/0.49    ~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f867])).
% 0.22/0.49  fof(f867,plain,(
% 0.22/0.49    $false | (~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f866,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    (sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f30,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k4_lattices(sK0,k6_lattices(sK0),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X1] : (k4_lattices(sK0,k6_lattices(sK0),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) => (sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).
% 0.22/0.49  fof(f866,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f865,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    v6_lattices(sK0) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl5_1 <=> v6_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f865,plain,(
% 0.22/0.49    ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f864,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    l1_lattices(sK0) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl5_2 <=> l1_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f864,plain,(
% 0.22/0.49    ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f863,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f863,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f862,f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~spl5_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl5_15 <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.49  fof(f862,plain,(
% 0.22/0.49    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_15 | ~spl5_28 | spl5_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f848,f312])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0)) | spl5_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f310])).
% 0.22/0.49  fof(f310,plain,(
% 0.22/0.49    spl5_32 <=> sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.22/0.49  fof(f848,plain,(
% 0.22/0.49    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_15 | ~spl5_28)),
% 0.22/0.49    inference(superposition,[],[f48,f844])).
% 0.22/0.49  fof(f844,plain,(
% 0.22/0.49    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | (~spl5_6 | ~spl5_15 | ~spl5_28)),
% 0.22/0.49    inference(subsumption_resolution,[],[f843,f41])).
% 0.22/0.49  fof(f843,plain,(
% 0.22/0.49    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_15 | ~spl5_28)),
% 0.22/0.49    inference(subsumption_resolution,[],[f842,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    l3_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f842,plain,(
% 0.22/0.49    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_15 | ~spl5_28)),
% 0.22/0.49    inference(subsumption_resolution,[],[f841,f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v9_lattices(sK0) | ~spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl5_6 <=> v9_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f841,plain,(
% 0.22/0.49    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl5_15 | ~spl5_28)),
% 0.22/0.49    inference(subsumption_resolution,[],[f840,f45])).
% 0.22/0.49  fof(f840,plain,(
% 0.22/0.49    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl5_15 | ~spl5_28)),
% 0.22/0.49    inference(subsumption_resolution,[],[f833,f140])).
% 0.22/0.49  fof(f833,plain,(
% 0.22/0.49    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl5_28),
% 0.22/0.49    inference(superposition,[],[f49,f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~spl5_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f261])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    spl5_28 <=> k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0] : (((v9_lattices(X0) | ((sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0] : (? [X2] : (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(rectify,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  % (3222)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.22/0.49  fof(f724,plain,(
% 0.22/0.49    ~spl5_15 | ~spl5_32 | ~spl5_1 | ~spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f723,f83,f79,f310,f138])).
% 0.22/0.49  fof(f723,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | (~spl5_1 | ~spl5_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f722,f41])).
% 0.22/0.49  fof(f722,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl5_1 | ~spl5_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f721,f80])).
% 0.22/0.49  fof(f721,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f720,f84])).
% 0.22/0.49  fof(f720,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f708,f45])).
% 0.22/0.49  fof(f708,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(superposition,[],[f46,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f326,plain,(
% 0.22/0.49    spl5_11),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    $false | spl5_11),
% 0.22/0.49    inference(subsumption_resolution,[],[f324,f44])).
% 0.22/0.49  fof(f324,plain,(
% 0.22/0.49    ~l3_lattices(sK0) | spl5_11),
% 0.22/0.49    inference(resolution,[],[f124,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~l2_lattices(sK0) | spl5_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl5_11 <=> l2_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.49  fof(f320,plain,(
% 0.22/0.49    spl5_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f319])).
% 0.22/0.49  fof(f319,plain,(
% 0.22/0.49    $false | spl5_5),
% 0.22/0.49    inference(subsumption_resolution,[],[f97,f44])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~l3_lattices(sK0) | spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl5_5 <=> l3_lattices(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    spl5_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f275])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    $false | spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f274,f44])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    ~l3_lattices(sK0) | spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f273,f41])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f272,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    v10_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl5_1),
% 0.22/0.49    inference(resolution,[],[f81,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.49  % (3231)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ~v6_lattices(sK0) | spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    ~spl5_11 | ~spl5_15 | spl5_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f259,f261,f138,f122])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f258,f41])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f205,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v14_lattices(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v14_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f45,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X3] : (k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (k1_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ((k1_lattices(X0,sK4(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK4(X0,X1)) != X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k1_lattices(X0,sK4(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK4(X0,X1)) != X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(rectify,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    spl5_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f195])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    $false | spl5_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f194,f44])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ~l3_lattices(sK0) | spl5_2),
% 0.22/0.49    inference(resolution,[],[f85,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ~l1_lattices(sK0) | spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~spl5_5 | spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f160,f99,f95])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f157,f41])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    v9_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.49    inference(resolution,[],[f42,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~spl5_11 | spl5_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f73,f138,f122])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 0.22/0.49    inference(resolution,[],[f41,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (3237)------------------------------
% 0.22/0.49  % (3237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3237)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (3237)Memory used [KB]: 6396
% 0.22/0.49  % (3237)Time elapsed: 0.059 s
% 0.22/0.49  % (3237)------------------------------
% 0.22/0.49  % (3237)------------------------------
% 0.22/0.50  % (3216)Success in time 0.131 s
%------------------------------------------------------------------------------
