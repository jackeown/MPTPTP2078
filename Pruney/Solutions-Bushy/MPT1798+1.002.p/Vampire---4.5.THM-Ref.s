%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1798+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 626 expanded)
%              Number of leaves         :   23 ( 243 expanded)
%              Depth                    :   19
%              Number of atoms          :  595 (4570 expanded)
%              Number of equality atoms :  150 (1589 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f167,f171,f178,f182,f201,f205,f211,f629,f645,f1269])).

% (10925)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f1269,plain,
    ( spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f1268])).

fof(f1268,plain,
    ( $false
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1267,f131])).

fof(f131,plain,
    ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_11
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1267,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1266,f36])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( u1_pre_topc(k8_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2)
        & u1_struct_0(sK1) = sK2
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK1)) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(sK0,X1)) != k5_tmap_1(sK0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (10923)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (10919)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (10922)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (10934)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (10921)Refutation not found, incomplete strategy% (10921)------------------------------
% (10921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10921)Termination reason: Refutation not found, incomplete strategy

% (10921)Memory used [KB]: 1663
% (10921)Time elapsed: 0.092 s
% (10921)------------------------------
% (10921)------------------------------
% (10916)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (10933)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f25,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( u1_pre_topc(k8_tmap_1(sK0,X1)) != k5_tmap_1(sK0,X2)
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( k5_tmap_1(sK0,X2) != u1_pre_topc(k8_tmap_1(sK0,sK1))
            & u1_struct_0(sK1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k5_tmap_1(sK0,X2) != u1_pre_topc(k8_tmap_1(sK0,sK1))
        & u1_struct_0(sK1) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( u1_pre_topc(k8_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2)
      & u1_struct_0(sK1) = sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) != k5_tmap_1(X0,X2)
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( u1_struct_0(X1) = X2
                   => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
              & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f1266,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1265,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1265,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1264,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1264,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f1263,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1263,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f1262])).

fof(f1262,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_11
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(superposition,[],[f170,f1183])).

fof(f1183,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl4_11
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1182,f131])).

fof(f1182,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1181,f34])).

fof(f1181,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1180,f33])).

fof(f1180,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1179,f32])).

fof(f1179,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_18 ),
    inference(resolution,[],[f166,f36])).

fof(f166,plain,
    ( ! [X4,X3] :
        ( ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | u1_struct_0(X3) = sK3(X4,X3,k6_tmap_1(sK0,u1_struct_0(sK1)))
        | k8_tmap_1(X4,X3) = k6_tmap_1(sK0,u1_struct_0(sK1)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_18
  <=> ! [X3,X4] :
        ( u1_struct_0(X3) = sK3(X4,X3,k6_tmap_1(sK0,u1_struct_0(sK1)))
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X3,X4)
        | k8_tmap_1(X4,X3) = k6_tmap_1(sK0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f170,plain,
    ( ! [X6,X5] :
        ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(X5,sK3(X5,X6,k6_tmap_1(sK0,u1_struct_0(sK1))))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(X6,X5)
        | k8_tmap_1(X5,X6) = k6_tmap_1(sK0,u1_struct_0(sK1)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_19
  <=> ! [X5,X6] :
        ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(X5,sK3(X5,X6,k6_tmap_1(sK0,u1_struct_0(sK1))))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(X6,X5)
        | k8_tmap_1(X5,X6) = k6_tmap_1(sK0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f645,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f644,f203,f161,f145,f130,f65,f60])).

fof(f60,plain,
    ( spl4_2
  <=> u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( spl4_3
  <=> u1_struct_0(sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f145,plain,
    ( spl4_13
  <=> l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f161,plain,
    ( spl4_17
  <=> v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f203,plain,
    ( spl4_23
  <=> ! [X7,X6] :
        ( k6_tmap_1(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
        | k5_tmap_1(sK0,u1_struct_0(sK1)) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f644,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK2)
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(backward_demodulation,[],[f263,f67])).

fof(f67,plain,
    ( u1_struct_0(sK1) = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f263,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(backward_demodulation,[],[f221,f132])).

fof(f132,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f221,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(superposition,[],[f204,f184])).

fof(f184,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f183,f146])).

fof(f146,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f183,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_17 ),
    inference(resolution,[],[f162,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f162,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f204,plain,
    ( ! [X6,X7] :
        ( k6_tmap_1(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
        | k5_tmap_1(sK0,u1_struct_0(sK1)) = X7 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f629,plain,
    ( spl4_1
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f598,f199,f161,f145,f130,f56])).

fof(f56,plain,
    ( spl4_1
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f199,plain,
    ( spl4_22
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != k6_tmap_1(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f598,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f220,f132])).

fof(f220,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f215])).

fof(f215,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_22 ),
    inference(superposition,[],[f200,f184])).

fof(f200,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != k6_tmap_1(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK0) = X2 )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f199])).

fof(f211,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f209,f32])).

fof(f209,plain,
    ( v2_struct_0(sK0)
    | spl4_21 ),
    inference(subsumption_resolution,[],[f208,f33])).

fof(f208,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_21 ),
    inference(subsumption_resolution,[],[f207,f34])).

fof(f207,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_21 ),
    inference(subsumption_resolution,[],[f206,f110])).

fof(f110,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f36])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f206,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_21 ),
    inference(resolution,[],[f197,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(f197,plain,
    ( ~ m1_subset_1(k5_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_21
  <=> m1_subset_1(k5_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f205,plain,
    ( ~ spl4_21
    | spl4_23 ),
    inference(avatar_split_clause,[],[f193,f203,f195])).

fof(f193,plain,(
    ! [X6,X7] :
      ( k6_tmap_1(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
      | k5_tmap_1(sK0,u1_struct_0(sK1)) = X7
      | ~ m1_subset_1(k5_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f49,f186])).

fof(f186,plain,(
    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f101,f110])).

fof(f101,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X7) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f100,f32])).

fof(f100,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X7) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X7))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f34])).

fof(f79,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k6_tmap_1(sK0,X7) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X7))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f201,plain,
    ( ~ spl4_21
    | spl4_22 ),
    inference(avatar_split_clause,[],[f191,f199,f195])).

fof(f191,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != k6_tmap_1(sK0,u1_struct_0(sK1))
      | u1_struct_0(sK0) = X2
      | ~ m1_subset_1(k5_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f48,f186])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f182,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f180,f110])).

fof(f180,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_17 ),
    inference(resolution,[],[f163,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_pre_topc(k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_pre_topc(k6_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f34])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v1_pre_topc(k6_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

% (10932)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f163,plain,
    ( ~ v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f178,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f176,f110])).

fof(f176,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_13 ),
    inference(resolution,[],[f147,f85])).

fof(f85,plain,(
    ! [X2] :
      ( l1_pre_topc(k6_tmap_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f84,f32])).

fof(f84,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | l1_pre_topc(k6_tmap_1(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f147,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f171,plain,
    ( ~ spl4_17
    | ~ spl4_13
    | spl4_19 ),
    inference(avatar_split_clause,[],[f138,f169,f145,f161])).

fof(f138,plain,(
    ! [X6,X5] :
      ( k6_tmap_1(sK0,u1_struct_0(sK1)) != k6_tmap_1(X5,sK3(X5,X6,k6_tmap_1(sK0,u1_struct_0(sK1))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
      | k8_tmap_1(X5,X6) = k6_tmap_1(sK0,u1_struct_0(sK1))
      | ~ v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
      | ~ m1_pre_topc(X6,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f112,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X2)
      | k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f112,plain,(
    v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f110,f83])).

fof(f83,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f82,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f75,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_pre_topc(k6_tmap_1(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f167,plain,
    ( ~ spl4_17
    | ~ spl4_13
    | spl4_18 ),
    inference(avatar_split_clause,[],[f137,f165,f145,f161])).

fof(f137,plain,(
    ! [X4,X3] :
      ( u1_struct_0(X3) = sK3(X4,X3,k6_tmap_1(sK0,u1_struct_0(sK1)))
      | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
      | k8_tmap_1(X4,X3) = k6_tmap_1(sK0,u1_struct_0(sK1))
      | ~ v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X2)
      | u1_struct_0(X1) = sK3(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f38,f65,f56])).

fof(f38,plain,
    ( u1_struct_0(sK1) = sK2
    | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f60,f56])).

fof(f39,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2)
    | u1_struct_0(sK0) != u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
