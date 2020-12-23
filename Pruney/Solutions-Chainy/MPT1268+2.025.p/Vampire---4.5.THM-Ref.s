%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 320 expanded)
%              Number of leaves         :   21 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  468 (2781 expanded)
%              Number of equality atoms :   64 ( 428 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f98,f381,f382,f384,f527])).

fof(f527,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f88,f487])).

fof(f487,plain,
    ( ! [X0] : ~ r1_tarski(sK2,X0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f486,f78])).

fof(f78,plain,
    ( k1_xboole_0 != sK2
    | spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f486,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f483,f131])).

fof(f131,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f130,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(condensation,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f483,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = sK2
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(resolution,[],[f481,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

% (14338)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (14342)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (14333)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (14328)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (14334)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (14330)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (14339)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (14326)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (14319)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f481,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f480,f88])).

fof(f480,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f479,f83])).

fof(f83,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f479,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(resolution,[],[f465,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f465,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X3,k1_xboole_0)
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f311,f188])).

fof(f188,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_16
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f311,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | r1_tarski(X3,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X3,sK1) ) ),
    inference(subsumption_resolution,[],[f310,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f310,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(X3,sK0)
      | r1_tarski(X3,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f88,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f384,plain,
    ( spl4_1
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f383,f186,f72])).

fof(f72,plain,
    ( spl4_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f383,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f293,f44])).

fof(f293,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f292,f188])).

fof(f292,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f382,plain,
    ( spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f375,f96,f186])).

fof(f96,plain,
    ( spl4_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f375,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f374,f158])).

fof(f158,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f156,f44])).

fof(f156,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f45])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f374,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f288,f45])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | k1_xboole_0 = k1_tops_1(sK0,X0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f287,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f287,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f285,f44])).

fof(f285,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f155,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f155,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK0)
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,sK1) )
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK1)
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,sK1)
        | ~ v3_pre_topc(X4,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f142,f110])).

fof(f110,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X1,X0)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,sK1)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f63,f97])).

fof(f97,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f381,plain,
    ( spl4_16
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f380,f72,f186])).

fof(f380,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f279,f44])).

fof(f279,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f45])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,
    ( spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f46,f96,f72])).

fof(f46,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f47,f91,f72])).

fof(f47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f48,f86,f72])).

fof(f48,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f49,f81,f72])).

fof(f49,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f50,f76,f72])).

fof(f50,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14329)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.47  % (14325)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (14324)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (14337)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (14323)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (14332)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (14340)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (14321)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (14320)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (14346)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (14331)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (14324)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f528,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f98,f381,f382,f384,f527])).
% 0.20/0.50  fof(f527,plain,(
% 0.20/0.50    spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_16),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f521])).
% 0.20/0.50  fof(f521,plain,(
% 0.20/0.50    $false | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f88,f487])).
% 0.20/0.50  fof(f487,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK2,X0)) ) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f486,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    k1_xboole_0 != sK2 | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl4_2 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f486,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = sK2 | ~r1_tarski(sK2,X0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f483,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(resolution,[],[f130,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(condensation,[],[f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(superposition,[],[f66,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.50  fof(f483,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = sK2 | ~r1_tarski(sK2,X0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_16)),
% 0.20/0.50    inference(resolution,[],[f481,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.20/0.50  % (14338)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (14342)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (14333)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (14328)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (14334)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (14330)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (14339)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (14326)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (14319)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  fof(f481,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f480,f88])).
% 0.20/0.51  fof(f480,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | ~r1_tarski(sK2,sK1) | (~spl4_3 | ~spl4_5 | ~spl4_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f479,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    v3_pre_topc(sK2,sK0) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl4_3 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f479,plain,(
% 0.20/0.51    r1_tarski(sK2,k1_xboole_0) | ~v3_pre_topc(sK2,sK0) | ~r1_tarski(sK2,sK1) | (~spl4_5 | ~spl4_16)),
% 0.20/0.51    inference(resolution,[],[f465,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X3,k1_xboole_0) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1)) ) | ~spl4_16),
% 0.20/0.51    inference(backward_demodulation,[],[f311,f188])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl4_16 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.51  fof(f311,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | r1_tarski(X3,k1_tops_1(sK0,sK1)) | ~r1_tarski(X3,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f310,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(rectify,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.51  fof(f310,plain,(
% 0.20/0.51    ( ! [X3] : (~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | r1_tarski(X3,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f54,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    r1_tarski(sK2,sK1) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl4_4 <=> r1_tarski(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f384,plain,(
% 0.20/0.51    spl4_1 | ~spl4_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f383,f186,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl4_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f383,plain,(
% 0.20/0.51    v2_tops_1(sK1,sK0) | ~spl4_16),
% 0.20/0.51    inference(subsumption_resolution,[],[f293,f44])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_16),
% 0.20/0.51    inference(subsumption_resolution,[],[f292,f188])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f53,f45])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.51  fof(f382,plain,(
% 0.20/0.51    spl4_16 | ~spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f375,f96,f186])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl4_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f375,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl4_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f374,f158])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f156,f44])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f51,f45])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.51  fof(f374,plain,(
% 0.20/0.51    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f288,f45])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | k1_xboole_0 = k1_tops_1(sK0,X0)) ) | ~spl4_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f287,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | ~spl4_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f285,f44])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f155,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    ( ! [X4] : (~v3_pre_topc(X4,sK0) | k1_xboole_0 = X4 | ~r1_tarski(X4,sK1)) ) | ~spl4_6),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X4] : (~r1_tarski(X4,sK1) | k1_xboole_0 = X4 | ~r1_tarski(X4,sK1) | ~v3_pre_topc(X4,sK0)) ) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f142,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(resolution,[],[f62,f45])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X1,X0) | k1_xboole_0 = X1 | ~r1_tarski(X1,sK1) | ~v3_pre_topc(X1,sK0)) ) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f68,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0)) ) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f63,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.51  fof(f381,plain,(
% 0.20/0.51    spl4_16 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f380,f72,f186])).
% 0.20/0.51  fof(f380,plain,(
% 0.20/0.51    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f279,f44])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.51    inference(resolution,[],[f52,f45])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl4_1 | spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f96,f72])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ~spl4_1 | spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f91,f72])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~spl4_1 | spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f86,f72])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~spl4_1 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f81,f72])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f76,f72])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (14324)------------------------------
% 0.20/0.51  % (14324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14324)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.52  % (14324)Memory used [KB]: 6268
% 0.20/0.52  % (14324)Time elapsed: 0.106 s
% 0.20/0.52  % (14324)------------------------------
% 0.20/0.52  % (14324)------------------------------
% 0.20/0.52  % (14318)Success in time 0.164 s
%------------------------------------------------------------------------------
