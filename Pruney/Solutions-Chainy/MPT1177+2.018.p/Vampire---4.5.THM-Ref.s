%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 961 expanded)
%              Number of leaves         :   23 ( 358 expanded)
%              Depth                    :   23
%              Number of atoms          :  835 (9378 expanded)
%              Number of equality atoms :   51 (  80 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28592)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (28582)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (28586)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (28582)Refutation not found, incomplete strategy% (28582)------------------------------
% (28582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28590)Refutation not found, incomplete strategy% (28590)------------------------------
% (28590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28590)Termination reason: Refutation not found, incomplete strategy

% (28590)Memory used [KB]: 6140
% (28590)Time elapsed: 0.125 s
% (28590)------------------------------
% (28590)------------------------------
% (28582)Termination reason: Refutation not found, incomplete strategy

% (28582)Memory used [KB]: 6140
% (28582)Time elapsed: 0.126 s
% (28582)------------------------------
% (28582)------------------------------
% (28577)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (28603)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (28577)Refutation not found, incomplete strategy% (28577)------------------------------
% (28577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28577)Termination reason: Refutation not found, incomplete strategy

% (28577)Memory used [KB]: 10618
% (28577)Time elapsed: 0.132 s
% (28577)------------------------------
% (28577)------------------------------
fof(f571,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f108,f124,f148,f179,f514,f525,f542,f544,f556,f570])).

fof(f570,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(global_subsumption,[],[f533,f106])).

fof(f106,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f533,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f77,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f77,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f556,plain,
    ( ~ spl4_6
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f554,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f554,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f553,f45])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f553,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f552,f46])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f552,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f551,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f551,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f550,f48])).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f550,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f549,f116])).

fof(f116,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f49,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f549,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f548,f524])).

fof(f524,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl4_8
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f548,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f146,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f146,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_6
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f544,plain,
    ( spl4_6
    | spl4_7
    | spl4_2 ),
    inference(avatar_split_clause,[],[f543,f80,f517,f145])).

fof(f517,plain,
    ( spl4_7
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f80,plain,
    ( spl4_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f543,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f201,f82])).

fof(f82,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f201,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f162,f51])).

fof(f51,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f161,f44])).

fof(f161,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f45])).

fof(f160,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f46])).

fof(f159,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f47])).

fof(f158,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f48])).

fof(f157,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f49])).

fof(f155,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_orders_2(X3,X0,X1)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | m1_orders_2(X2,X0,X3)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f542,plain,
    ( ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f541])).

fof(f541,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f535,f59])).

fof(f59,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f535,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f77,f519])).

fof(f519,plain,
    ( sK2 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f517])).

fof(f525,plain,
    ( ~ spl4_8
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f150,f105,f517,f522])).

fof(f150,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f107,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f107,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f514,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f512,f44])).

fof(f512,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f511,f45])).

fof(f511,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f510,f46])).

fof(f510,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f509,f47])).

fof(f509,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f508,f48])).

fof(f508,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f507,f49])).

fof(f507,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f490,f182])).

fof(f182,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f51,f143])).

fof(f143,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f490,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f232,f182])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_orders_2(X0,X1,X2)
      | ~ m2_orders_2(k1_xboole_0,X1,X2)
      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f199,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

fof(f199,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f87,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f69,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f71,f72])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f179,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f177,f174])).

fof(f174,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f81,f152])).

fof(f152,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f149,f78])).

fof(f78,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f149,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f107,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f177,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | spl4_1
    | ~ spl4_4
    | spl4_6 ),
    inference(superposition,[],[f147,f152])).

fof(f147,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f139,f80,f145,f141])).

fof(f139,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f138,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f135,f47])).

fof(f135,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f134,f48])).

fof(f134,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f133,f130])).

fof(f130,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f129,f44])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f47])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f48])).

fof(f125,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f51])).

fof(f133,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f132,f116])).

fof(f132,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f58,f81])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f124,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f122,f44])).

fof(f122,plain,
    ( v2_struct_0(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f121,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f120,f46])).

fof(f120,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f119,f47])).

fof(f119,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f118,f48])).

fof(f118,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f117,f49])).

fof(f117,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f110,f103])).

fof(f103,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f99,f80,f105,f101])).

fof(f99,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f98,f44])).

fof(f98,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f97,f45])).

fof(f97,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f95,f47])).

fof(f95,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f94,f48])).

fof(f94,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f57,f81])).

fof(f84,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f52,f80,f76])).

fof(f52,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f80,f76])).

fof(f53,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:07:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (28598)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.49  % (28589)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (28581)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (28597)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (28602)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (28585)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (28595)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (28588)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (28590)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (28579)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (28583)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (28584)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (28578)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (28583)Refutation not found, incomplete strategy% (28583)------------------------------
% 0.22/0.52  % (28583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28583)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28583)Memory used [KB]: 10618
% 0.22/0.52  % (28583)Time elapsed: 0.114 s
% 0.22/0.52  % (28583)------------------------------
% 0.22/0.52  % (28583)------------------------------
% 0.22/0.52  % (28599)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (28601)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (28594)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (28587)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (28600)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (28580)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (28588)Refutation not found, incomplete strategy% (28588)------------------------------
% 0.22/0.53  % (28588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28588)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28588)Memory used [KB]: 10618
% 0.22/0.53  % (28588)Time elapsed: 0.121 s
% 0.22/0.53  % (28588)------------------------------
% 0.22/0.53  % (28588)------------------------------
% 0.22/0.53  % (28593)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (28587)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  % (28592)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (28582)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (28586)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (28582)Refutation not found, incomplete strategy% (28582)------------------------------
% 0.22/0.54  % (28582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28590)Refutation not found, incomplete strategy% (28590)------------------------------
% 0.22/0.54  % (28590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28590)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28590)Memory used [KB]: 6140
% 0.22/0.54  % (28590)Time elapsed: 0.125 s
% 0.22/0.54  % (28590)------------------------------
% 0.22/0.54  % (28590)------------------------------
% 0.22/0.54  % (28582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28582)Memory used [KB]: 6140
% 0.22/0.54  % (28582)Time elapsed: 0.126 s
% 0.22/0.54  % (28582)------------------------------
% 0.22/0.54  % (28582)------------------------------
% 1.39/0.54  % (28577)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.39/0.54  % (28603)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.54  % (28577)Refutation not found, incomplete strategy% (28577)------------------------------
% 1.39/0.54  % (28577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (28577)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (28577)Memory used [KB]: 10618
% 1.39/0.54  % (28577)Time elapsed: 0.132 s
% 1.39/0.54  % (28577)------------------------------
% 1.39/0.54  % (28577)------------------------------
% 1.39/0.55  fof(f571,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(avatar_sat_refutation,[],[f83,f84,f108,f124,f148,f179,f514,f525,f542,f544,f556,f570])).
% 1.39/0.55  fof(f570,plain,(
% 1.39/0.55    ~spl4_1 | spl4_4),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f569])).
% 1.39/0.55  fof(f569,plain,(
% 1.39/0.55    $false | (~spl4_1 | spl4_4)),
% 1.39/0.55    inference(global_subsumption,[],[f533,f106])).
% 1.39/0.55  fof(f106,plain,(
% 1.39/0.55    ~r1_tarski(sK2,sK3) | spl4_4),
% 1.39/0.55    inference(avatar_component_clause,[],[f105])).
% 1.39/0.55  fof(f105,plain,(
% 1.39/0.55    spl4_4 <=> r1_tarski(sK2,sK3)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.39/0.55  fof(f533,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~spl4_1),
% 1.39/0.55    inference(resolution,[],[f77,f65])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.39/0.55    inference(flattening,[],[f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.39/0.55  fof(f77,plain,(
% 1.39/0.55    r2_xboole_0(sK2,sK3) | ~spl4_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f76])).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    spl4_1 <=> r2_xboole_0(sK2,sK3)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.39/0.55  fof(f556,plain,(
% 1.39/0.55    ~spl4_6 | spl4_8),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f555])).
% 1.39/0.55  fof(f555,plain,(
% 1.39/0.55    $false | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f554,f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ~v2_struct_0(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f17])).
% 1.39/0.55  fof(f17,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f16])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,negated_conjecture,(
% 1.39/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.39/0.55    inference(negated_conjecture,[],[f12])).
% 1.39/0.55  fof(f12,conjecture,(
% 1.39/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 1.39/0.55  fof(f554,plain,(
% 1.39/0.55    v2_struct_0(sK0) | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f553,f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    v3_orders_2(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f553,plain,(
% 1.39/0.55    ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f552,f46])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    v4_orders_2(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f552,plain,(
% 1.39/0.55    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f551,f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    v5_orders_2(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f551,plain,(
% 1.39/0.55    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f550,f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    l1_orders_2(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f550,plain,(
% 1.39/0.55    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f549,f116])).
% 1.39/0.55  fof(f116,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.55    inference(subsumption_resolution,[],[f115,f44])).
% 1.39/0.55  fof(f115,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f114,f45])).
% 1.39/0.55  fof(f114,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f113,f46])).
% 1.39/0.55  fof(f113,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f112,f47])).
% 1.39/0.55  fof(f112,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f111,f48])).
% 1.39/0.55  fof(f111,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f109,f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f109,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(resolution,[],[f60,f50])).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    m2_orders_2(sK2,sK0,sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f60,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,plain,(
% 1.39/0.55    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.55    inference(pure_predicate_removal,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.39/0.55  fof(f549,plain,(
% 1.39/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_6 | spl4_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f548,f524])).
% 1.39/0.55  fof(f524,plain,(
% 1.39/0.55    ~r1_tarski(sK3,sK2) | spl4_8),
% 1.39/0.55    inference(avatar_component_clause,[],[f522])).
% 1.39/0.55  fof(f522,plain,(
% 1.39/0.55    spl4_8 <=> r1_tarski(sK3,sK2)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.39/0.55  fof(f548,plain,(
% 1.39/0.55    r1_tarski(sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_6),
% 1.39/0.55    inference(resolution,[],[f146,f57])).
% 1.39/0.55  fof(f57,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f23])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 1.39/0.55  fof(f146,plain,(
% 1.39/0.55    m1_orders_2(sK3,sK0,sK2) | ~spl4_6),
% 1.39/0.55    inference(avatar_component_clause,[],[f145])).
% 1.39/0.55  fof(f145,plain,(
% 1.39/0.55    spl4_6 <=> m1_orders_2(sK3,sK0,sK2)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.39/0.55  fof(f544,plain,(
% 1.39/0.55    spl4_6 | spl4_7 | spl4_2),
% 1.39/0.55    inference(avatar_split_clause,[],[f543,f80,f517,f145])).
% 1.39/0.55  fof(f517,plain,(
% 1.39/0.55    spl4_7 <=> sK2 = sK3),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.39/0.55  fof(f80,plain,(
% 1.39/0.55    spl4_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.39/0.55  fof(f543,plain,(
% 1.39/0.55    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f201,f82])).
% 1.39/0.55  fof(f82,plain,(
% 1.39/0.55    ~m1_orders_2(sK2,sK0,sK3) | spl4_2),
% 1.39/0.55    inference(avatar_component_clause,[],[f80])).
% 1.39/0.55  fof(f201,plain,(
% 1.39/0.55    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 1.39/0.55    inference(resolution,[],[f162,f51])).
% 1.39/0.55  fof(f51,plain,(
% 1.39/0.55    m2_orders_2(sK3,sK0,sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f162,plain,(
% 1.39/0.55    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f161,f44])).
% 1.39/0.55  fof(f161,plain,(
% 1.39/0.55    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f160,f45])).
% 1.39/0.55  fof(f160,plain,(
% 1.39/0.55    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f159,f46])).
% 1.39/0.55  fof(f159,plain,(
% 1.39/0.55    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f158,f47])).
% 1.39/0.55  fof(f158,plain,(
% 1.39/0.55    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f157,f48])).
% 1.39/0.55  fof(f157,plain,(
% 1.39/0.55    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f155,f49])).
% 1.39/0.55  fof(f155,plain,(
% 1.39/0.55    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(resolution,[],[f56,f50])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~m2_orders_2(X3,X0,X1) | m1_orders_2(X3,X0,X2) | X2 = X3 | m1_orders_2(X2,X0,X3) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 1.39/0.55  fof(f542,plain,(
% 1.39/0.55    ~spl4_1 | ~spl4_7),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f541])).
% 1.39/0.55  fof(f541,plain,(
% 1.39/0.55    $false | (~spl4_1 | ~spl4_7)),
% 1.39/0.55    inference(subsumption_resolution,[],[f535,f59])).
% 1.39/0.55  fof(f59,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,plain,(
% 1.39/0.55    ! [X0] : ~r2_xboole_0(X0,X0)),
% 1.39/0.55    inference(rectify,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 1.39/0.55  fof(f535,plain,(
% 1.39/0.55    r2_xboole_0(sK2,sK2) | (~spl4_1 | ~spl4_7)),
% 1.39/0.55    inference(superposition,[],[f77,f519])).
% 1.39/0.55  fof(f519,plain,(
% 1.39/0.55    sK2 = sK3 | ~spl4_7),
% 1.39/0.55    inference(avatar_component_clause,[],[f517])).
% 1.39/0.55  fof(f525,plain,(
% 1.39/0.55    ~spl4_8 | spl4_7 | ~spl4_4),
% 1.39/0.55    inference(avatar_split_clause,[],[f150,f105,f517,f522])).
% 1.39/0.55  fof(f150,plain,(
% 1.39/0.55    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl4_4),
% 1.39/0.55    inference(resolution,[],[f107,f64])).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f40])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f107,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~spl4_4),
% 1.39/0.55    inference(avatar_component_clause,[],[f105])).
% 1.39/0.55  fof(f514,plain,(
% 1.39/0.55    ~spl4_5),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f513])).
% 1.39/0.55  fof(f513,plain,(
% 1.39/0.55    $false | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f512,f44])).
% 1.39/0.55  fof(f512,plain,(
% 1.39/0.55    v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f511,f45])).
% 1.39/0.55  fof(f511,plain,(
% 1.39/0.55    ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f510,f46])).
% 1.39/0.55  fof(f510,plain,(
% 1.39/0.55    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f509,f47])).
% 1.39/0.55  fof(f509,plain,(
% 1.39/0.55    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f508,f48])).
% 1.39/0.55  fof(f508,plain,(
% 1.39/0.55    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f507,f49])).
% 1.39/0.55  fof(f507,plain,(
% 1.39/0.55    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f490,f182])).
% 1.39/0.55  fof(f182,plain,(
% 1.39/0.55    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl4_5),
% 1.39/0.55    inference(superposition,[],[f51,f143])).
% 1.39/0.55  fof(f143,plain,(
% 1.39/0.55    k1_xboole_0 = sK3 | ~spl4_5),
% 1.39/0.55    inference(avatar_component_clause,[],[f141])).
% 1.39/0.55  fof(f141,plain,(
% 1.39/0.55    spl4_5 <=> k1_xboole_0 = sK3),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.39/0.55  fof(f490,plain,(
% 1.39/0.55    ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.39/0.55    inference(resolution,[],[f232,f182])).
% 1.39/0.55  fof(f232,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m2_orders_2(X0,X1,X2) | ~m2_orders_2(k1_xboole_0,X1,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.39/0.55    inference(resolution,[],[f199,f54])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f19])).
% 1.39/0.55  fof(f19,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f18])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 1.39/0.55  fof(f199,plain,(
% 1.39/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(superposition,[],[f87,f85])).
% 1.39/0.55  fof(f85,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.39/0.55    inference(resolution,[],[f69,f72])).
% 1.39/0.55  fof(f72,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f63])).
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f40])).
% 1.39/0.55  fof(f69,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.39/0.55    inference(nnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.39/0.55  fof(f87,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.39/0.55    inference(resolution,[],[f71,f72])).
% 1.39/0.55  fof(f71,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f30])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.39/0.55  fof(f179,plain,(
% 1.39/0.55    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_6),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f178])).
% 1.39/0.55  fof(f178,plain,(
% 1.39/0.55    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_6)),
% 1.39/0.55    inference(subsumption_resolution,[],[f177,f174])).
% 1.39/0.55  fof(f174,plain,(
% 1.39/0.55    m1_orders_2(sK2,sK0,sK2) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.39/0.55    inference(superposition,[],[f81,f152])).
% 1.39/0.55  fof(f152,plain,(
% 1.39/0.55    sK2 = sK3 | (spl4_1 | ~spl4_4)),
% 1.39/0.55    inference(subsumption_resolution,[],[f149,f78])).
% 1.39/0.55  fof(f78,plain,(
% 1.39/0.55    ~r2_xboole_0(sK2,sK3) | spl4_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f76])).
% 1.39/0.55  fof(f149,plain,(
% 1.39/0.55    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_4),
% 1.39/0.55    inference(resolution,[],[f107,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f81,plain,(
% 1.39/0.55    m1_orders_2(sK2,sK0,sK3) | ~spl4_2),
% 1.39/0.55    inference(avatar_component_clause,[],[f80])).
% 1.39/0.55  fof(f177,plain,(
% 1.39/0.55    ~m1_orders_2(sK2,sK0,sK2) | (spl4_1 | ~spl4_4 | spl4_6)),
% 1.39/0.55    inference(superposition,[],[f147,f152])).
% 1.39/0.55  fof(f147,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | spl4_6),
% 1.39/0.55    inference(avatar_component_clause,[],[f145])).
% 1.39/0.55  fof(f148,plain,(
% 1.39/0.55    spl4_5 | ~spl4_6 | ~spl4_2),
% 1.39/0.55    inference(avatar_split_clause,[],[f139,f80,f145,f141])).
% 1.39/0.55  fof(f139,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f138,f44])).
% 1.39/0.55  fof(f138,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f137,f45])).
% 1.39/0.55  fof(f137,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f136,f46])).
% 1.39/0.55  fof(f136,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f135,f47])).
% 1.39/0.55  fof(f135,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f134,f48])).
% 1.39/0.55  fof(f134,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f133,f130])).
% 1.39/0.55  fof(f130,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.55    inference(subsumption_resolution,[],[f129,f44])).
% 1.39/0.55  fof(f129,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f128,f45])).
% 1.39/0.55  fof(f128,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f127,f46])).
% 1.39/0.55  fof(f127,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f126,f47])).
% 1.39/0.55  fof(f126,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f125,f48])).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f110,f49])).
% 1.39/0.55  fof(f110,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(resolution,[],[f60,f51])).
% 1.39/0.55  fof(f133,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f132,f116])).
% 1.39/0.55  fof(f132,plain,(
% 1.39/0.55    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(resolution,[],[f58,f81])).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f24])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 1.39/0.55  fof(f124,plain,(
% 1.39/0.55    spl4_3),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f123])).
% 1.39/0.55  fof(f123,plain,(
% 1.39/0.55    $false | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f122,f44])).
% 1.39/0.55  fof(f122,plain,(
% 1.39/0.55    v2_struct_0(sK0) | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f121,f45])).
% 1.39/0.55  fof(f121,plain,(
% 1.39/0.55    ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f120,f46])).
% 1.39/0.55  fof(f120,plain,(
% 1.39/0.55    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f119,f47])).
% 1.39/0.55  fof(f119,plain,(
% 1.39/0.55    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f118,f48])).
% 1.39/0.55  fof(f118,plain,(
% 1.39/0.55    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f117,f49])).
% 1.39/0.55  fof(f117,plain,(
% 1.39/0.55    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl4_3),
% 1.39/0.55    inference(subsumption_resolution,[],[f110,f103])).
% 1.39/0.55  fof(f103,plain,(
% 1.39/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_3),
% 1.39/0.55    inference(avatar_component_clause,[],[f101])).
% 1.39/0.55  fof(f101,plain,(
% 1.39/0.55    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.39/0.55  fof(f108,plain,(
% 1.39/0.55    ~spl4_3 | spl4_4 | ~spl4_2),
% 1.39/0.55    inference(avatar_split_clause,[],[f99,f80,f105,f101])).
% 1.39/0.55  fof(f99,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f98,f44])).
% 1.39/0.55  fof(f98,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f97,f45])).
% 1.39/0.55  fof(f97,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f96,f46])).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f95,f47])).
% 1.39/0.55  fof(f95,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(subsumption_resolution,[],[f94,f48])).
% 1.39/0.55  fof(f94,plain,(
% 1.39/0.55    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_2),
% 1.39/0.55    inference(resolution,[],[f57,f81])).
% 1.39/0.55  fof(f84,plain,(
% 1.39/0.55    spl4_1 | spl4_2),
% 1.39/0.55    inference(avatar_split_clause,[],[f52,f80,f76])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f83,plain,(
% 1.39/0.55    ~spl4_1 | ~spl4_2),
% 1.39/0.55    inference(avatar_split_clause,[],[f53,f80,f76])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (28587)------------------------------
% 1.39/0.55  % (28587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (28587)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (28587)Memory used [KB]: 10874
% 1.39/0.55  % (28587)Time elapsed: 0.121 s
% 1.39/0.55  % (28587)------------------------------
% 1.39/0.55  % (28587)------------------------------
% 1.39/0.55  % (28573)Success in time 0.182 s
%------------------------------------------------------------------------------
