%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 186 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  361 ( 704 expanded)
%              Number of equality atoms :   28 (  67 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21039)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f103,f128,f138,f143,f160,f179,f181,f186,f191,f196,f257,f337,f357,f372])).

fof(f372,plain,
    ( spl9_18
    | ~ spl9_33 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl9_18
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f190,f366,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

% (21042)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (21037)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (21062)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (21047)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (21054)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (21057)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (21049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (21053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (21046)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (21036)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (21045)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (21055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (21061)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f366,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl9_33 ),
    inference(resolution,[],[f361,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f361,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,sK4(sK2,X2))
        | r1_tarski(sK2,X2) )
    | ~ spl9_33 ),
    inference(resolution,[],[f359,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f359,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r1_tarski(k1_xboole_0,X1) )
    | ~ spl9_33 ),
    inference(resolution,[],[f356,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f356,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl9_33
  <=> ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f190,plain,
    ( k1_xboole_0 != sK2
    | spl9_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f357,plain,
    ( ~ spl9_5
    | spl9_33
    | ~ spl9_3
    | ~ spl9_11
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f352,f335,f140,f91,f355,f100])).

fof(f100,plain,
    ( spl9_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f91,plain,
    ( spl9_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f140,plain,
    ( spl9_11
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f335,plain,
    ( spl9_31
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f352,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK2)
        | ~ r1_tarski(sK2,sK1) )
    | ~ spl9_3
    | ~ spl9_11
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f349,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f349,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(sK2,sK1) )
    | ~ spl9_3
    | ~ spl9_31 ),
    inference(resolution,[],[f336,f93])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f335])).

fof(f337,plain,
    ( ~ spl9_17
    | ~ spl9_1
    | spl9_31
    | ~ spl9_2
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f277,f193,f86,f335,f81,f183])).

fof(f183,plain,
    ( spl9_17
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f81,plain,
    ( spl9_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f86,plain,
    ( spl9_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f193,plain,
    ( spl9_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(sK2,sK0)
        | ~ r1_tarski(sK2,X0)
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | ~ spl9_19 ),
    inference(resolution,[],[f195,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f257,plain,
    ( ~ spl9_3
    | ~ spl9_10
    | spl9_11
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_10
    | spl9_11
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f137,f142,f93,f178])).

fof(f178,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,X2)
        | ~ r1_tarski(k1_tops_1(sK0,X2),sK1) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl9_16
  <=> ! [X2] :
        ( k1_xboole_0 = k1_tops_1(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

% (21063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f142,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f137,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl9_10
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f196,plain,
    ( ~ spl9_4
    | spl9_19 ),
    inference(avatar_split_clause,[],[f35,f193,f96])).

fof(f96,plain,
    ( spl9_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f191,plain,
    ( ~ spl9_4
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f38,f188,f96])).

fof(f38,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f186,plain,
    ( ~ spl9_4
    | spl9_17 ),
    inference(avatar_split_clause,[],[f37,f183,f96])).

fof(f37,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f181,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_11 ),
    inference(unit_resulting_resolution,[],[f88,f93,f142,f97,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f97,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f179,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_16
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f175,f158,f125,f177,f86,f81])).

fof(f125,plain,
    ( spl9_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f158,plain,
    ( spl9_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f175,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_tops_1(sK0,X2)
        | ~ r1_tarski(k1_tops_1(sK0,X2),sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(resolution,[],[f173,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f173,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK0)
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,sK1) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK1)
        | k1_xboole_0 = X4
        | ~ v3_pre_topc(X4,sK0)
        | ~ r1_tarski(X4,sK1) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(resolution,[],[f165,f127])).

fof(f127,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl9_15 ),
    inference(resolution,[],[f163,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f163,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = X2 )
    | ~ spl9_15 ),
    inference(resolution,[],[f159,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f159,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f160,plain,
    ( spl9_4
    | spl9_15 ),
    inference(avatar_split_clause,[],[f39,f158,f96])).

fof(f39,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,
    ( spl9_4
    | ~ spl9_11
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f105,f91,f86,f140,f96])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f138,plain,
    ( spl9_10
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f104,f91,f86,f135])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl9_3 ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f128,plain,
    ( spl9_8
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f112,f91,f125])).

fof(f112,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl9_3 ),
    inference(resolution,[],[f93,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f103,plain,
    ( ~ spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f36,f100,f96])).

fof(f36,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f42,f86])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f41,f81])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:39:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (21059)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (21051)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (21043)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (21048)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (21050)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (21041)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (21064)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.51  % (21058)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (21038)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (21056)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (21040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (21065)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (21058)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  % (21039)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  fof(f373,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f84,f89,f94,f103,f128,f138,f143,f160,f179,f181,f186,f191,f196,f257,f337,f357,f372])).
% 0.19/0.52  fof(f372,plain,(
% 0.19/0.52    spl9_18 | ~spl9_33),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f370])).
% 0.19/0.52  fof(f370,plain,(
% 0.19/0.52    $false | (spl9_18 | ~spl9_33)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f190,f366,f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  % (21042)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (21037)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (21062)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (21047)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (21054)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (21057)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (21049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (21053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  % (21046)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.53  % (21036)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (21045)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (21055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (21061)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.19/0.54  fof(f366,plain,(
% 0.19/0.54    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl9_33),
% 0.19/0.54    inference(resolution,[],[f361,f43])).
% 0.19/0.54  fof(f43,plain,(
% 0.19/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.54  fof(f361,plain,(
% 0.19/0.54    ( ! [X2] : (~r1_tarski(k1_xboole_0,sK4(sK2,X2)) | r1_tarski(sK2,X2)) ) | ~spl9_33),
% 0.19/0.54    inference(resolution,[],[f359,f63])).
% 0.19/0.54  fof(f63,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f31])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.54  fof(f359,plain,(
% 0.19/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r1_tarski(k1_xboole_0,X1)) ) | ~spl9_33),
% 0.19/0.54    inference(resolution,[],[f356,f67])).
% 0.19/0.54  fof(f67,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f32])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f12])).
% 0.19/0.54  fof(f12,axiom,(
% 0.19/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.54  fof(f356,plain,(
% 0.19/0.54    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK2)) ) | ~spl9_33),
% 0.19/0.54    inference(avatar_component_clause,[],[f355])).
% 0.19/0.54  fof(f355,plain,(
% 0.19/0.54    spl9_33 <=> ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK2))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.19/0.54  fof(f190,plain,(
% 0.19/0.54    k1_xboole_0 != sK2 | spl9_18),
% 0.19/0.54    inference(avatar_component_clause,[],[f188])).
% 0.19/0.54  fof(f188,plain,(
% 0.19/0.54    spl9_18 <=> k1_xboole_0 = sK2),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.19/0.54  fof(f357,plain,(
% 0.19/0.54    ~spl9_5 | spl9_33 | ~spl9_3 | ~spl9_11 | ~spl9_31),
% 0.19/0.54    inference(avatar_split_clause,[],[f352,f335,f140,f91,f355,f100])).
% 0.19/0.54  fof(f100,plain,(
% 0.19/0.54    spl9_5 <=> r1_tarski(sK2,sK1)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.19/0.54  fof(f91,plain,(
% 0.19/0.54    spl9_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.19/0.54  fof(f140,plain,(
% 0.19/0.54    spl9_11 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.19/0.54  fof(f335,plain,(
% 0.19/0.54    spl9_31 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK2,X0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.19/0.54  fof(f352,plain,(
% 0.19/0.54    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK2) | ~r1_tarski(sK2,sK1)) ) | (~spl9_3 | ~spl9_11 | ~spl9_31)),
% 0.19/0.54    inference(forward_demodulation,[],[f349,f141])).
% 0.19/0.54  fof(f141,plain,(
% 0.19/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl9_11),
% 0.19/0.54    inference(avatar_component_clause,[],[f140])).
% 0.19/0.54  fof(f349,plain,(
% 0.19/0.54    ( ! [X2] : (~r2_hidden(X2,sK2) | r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK2,sK1)) ) | (~spl9_3 | ~spl9_31)),
% 0.19/0.54    inference(resolution,[],[f336,f93])).
% 0.19/0.54  fof(f93,plain,(
% 0.19/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_3),
% 0.19/0.54    inference(avatar_component_clause,[],[f91])).
% 0.19/0.54  fof(f336,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK2,X0)) ) | ~spl9_31),
% 0.19/0.54    inference(avatar_component_clause,[],[f335])).
% 0.19/0.54  fof(f337,plain,(
% 0.19/0.54    ~spl9_17 | ~spl9_1 | spl9_31 | ~spl9_2 | ~spl9_19),
% 0.19/0.54    inference(avatar_split_clause,[],[f277,f193,f86,f335,f81,f183])).
% 0.19/0.54  fof(f183,plain,(
% 0.19/0.54    spl9_17 <=> v3_pre_topc(sK2,sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.19/0.54  fof(f81,plain,(
% 0.19/0.54    spl9_1 <=> v2_pre_topc(sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.19/0.54  fof(f86,plain,(
% 0.19/0.54    spl9_2 <=> l1_pre_topc(sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.19/0.54  fof(f193,plain,(
% 0.19/0.54    spl9_19 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.19/0.54  fof(f277,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~r1_tarski(sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0))) ) | ~spl9_19),
% 0.19/0.54    inference(resolution,[],[f195,f55])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f27])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,axiom,(
% 0.19/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 0.19/0.54  fof(f195,plain,(
% 0.19/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_19),
% 0.19/0.54    inference(avatar_component_clause,[],[f193])).
% 0.19/0.54  fof(f257,plain,(
% 0.19/0.54    ~spl9_3 | ~spl9_10 | spl9_11 | ~spl9_16),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f253])).
% 0.19/0.54  fof(f253,plain,(
% 0.19/0.54    $false | (~spl9_3 | ~spl9_10 | spl9_11 | ~spl9_16)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f137,f142,f93,f178])).
% 0.19/0.54  fof(f178,plain,(
% 0.19/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X2) | ~r1_tarski(k1_tops_1(sK0,X2),sK1)) ) | ~spl9_16),
% 0.19/0.54    inference(avatar_component_clause,[],[f177])).
% 0.19/0.54  fof(f177,plain,(
% 0.19/0.54    spl9_16 <=> ! [X2] : (k1_xboole_0 = k1_tops_1(sK0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X2),sK1))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.19/0.54  % (21063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  fof(f142,plain,(
% 0.19/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl9_11),
% 0.19/0.54    inference(avatar_component_clause,[],[f140])).
% 0.19/0.54  fof(f137,plain,(
% 0.19/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl9_10),
% 0.19/0.54    inference(avatar_component_clause,[],[f135])).
% 0.19/0.54  fof(f135,plain,(
% 0.19/0.54    spl9_10 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.19/0.54  fof(f196,plain,(
% 0.19/0.54    ~spl9_4 | spl9_19),
% 0.19/0.54    inference(avatar_split_clause,[],[f35,f193,f96])).
% 0.19/0.54  fof(f96,plain,(
% 0.19/0.54    spl9_4 <=> v2_tops_1(sK1,sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f20])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f19])).
% 0.19/0.54  fof(f19,negated_conjecture,(
% 0.19/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.19/0.54    inference(negated_conjecture,[],[f18])).
% 0.19/0.54  fof(f18,conjecture,(
% 0.19/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.19/0.54  fof(f191,plain,(
% 0.19/0.54    ~spl9_4 | ~spl9_18),
% 0.19/0.54    inference(avatar_split_clause,[],[f38,f188,f96])).
% 0.19/0.54  fof(f38,plain,(
% 0.19/0.54    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f186,plain,(
% 0.19/0.54    ~spl9_4 | spl9_17),
% 0.19/0.54    inference(avatar_split_clause,[],[f37,f183,f96])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f181,plain,(
% 0.19/0.54    ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_11),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f180])).
% 0.19/0.54  fof(f180,plain,(
% 0.19/0.54    $false | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_11)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f88,f93,f142,f97,f48])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.19/0.54  fof(f97,plain,(
% 0.19/0.54    v2_tops_1(sK1,sK0) | ~spl9_4),
% 0.19/0.54    inference(avatar_component_clause,[],[f96])).
% 0.19/0.54  fof(f88,plain,(
% 0.19/0.54    l1_pre_topc(sK0) | ~spl9_2),
% 0.19/0.54    inference(avatar_component_clause,[],[f86])).
% 0.19/0.54  fof(f179,plain,(
% 0.19/0.54    ~spl9_1 | ~spl9_2 | spl9_16 | ~spl9_8 | ~spl9_15),
% 0.19/0.54    inference(avatar_split_clause,[],[f175,f158,f125,f177,f86,f81])).
% 0.19/0.54  fof(f125,plain,(
% 0.19/0.54    spl9_8 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.19/0.54  fof(f158,plain,(
% 0.19/0.54    spl9_15 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.19/0.54  fof(f175,plain,(
% 0.19/0.54    ( ! [X2] : (k1_xboole_0 = k1_tops_1(sK0,X2) | ~r1_tarski(k1_tops_1(sK0,X2),sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl9_8 | ~spl9_15)),
% 0.19/0.54    inference(resolution,[],[f173,f61])).
% 0.19/0.54  fof(f61,plain,(
% 0.19/0.54    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f29])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f13])).
% 0.19/0.54  fof(f13,axiom,(
% 0.19/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.54  fof(f173,plain,(
% 0.19/0.54    ( ! [X4] : (~v3_pre_topc(X4,sK0) | k1_xboole_0 = X4 | ~r1_tarski(X4,sK1)) ) | (~spl9_8 | ~spl9_15)),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f171])).
% 0.19/0.54  fof(f171,plain,(
% 0.19/0.54    ( ! [X4] : (~r1_tarski(X4,sK1) | k1_xboole_0 = X4 | ~v3_pre_topc(X4,sK0) | ~r1_tarski(X4,sK1)) ) | (~spl9_8 | ~spl9_15)),
% 0.19/0.54    inference(resolution,[],[f165,f127])).
% 0.19/0.54  fof(f127,plain,(
% 0.19/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl9_8),
% 0.19/0.54    inference(avatar_component_clause,[],[f125])).
% 0.19/0.54  fof(f165,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1)) ) | ~spl9_15),
% 0.19/0.54    inference(resolution,[],[f163,f68])).
% 0.19/0.54  fof(f68,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(flattening,[],[f33])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.54    inference(ennf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.54  fof(f163,plain,(
% 0.19/0.54    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | k1_xboole_0 = X2) ) | ~spl9_15),
% 0.19/0.54    inference(resolution,[],[f159,f65])).
% 0.19/0.54  fof(f65,plain,(
% 0.19/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,axiom,(
% 0.19/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.54  fof(f159,plain,(
% 0.19/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1)) ) | ~spl9_15),
% 0.19/0.54    inference(avatar_component_clause,[],[f158])).
% 0.19/0.54  fof(f160,plain,(
% 0.19/0.54    spl9_4 | spl9_15),
% 0.19/0.54    inference(avatar_split_clause,[],[f39,f158,f96])).
% 0.19/0.54  fof(f39,plain,(
% 0.19/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f143,plain,(
% 0.19/0.54    spl9_4 | ~spl9_11 | ~spl9_2 | ~spl9_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f105,f91,f86,f140,f96])).
% 0.19/0.54  fof(f105,plain,(
% 0.19/0.54    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~spl9_3),
% 0.19/0.54    inference(resolution,[],[f93,f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f23])).
% 0.19/0.54  fof(f138,plain,(
% 0.19/0.54    spl9_10 | ~spl9_2 | ~spl9_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f104,f91,f86,f135])).
% 0.19/0.54  fof(f104,plain,(
% 0.19/0.54    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl9_3),
% 0.19/0.54    inference(resolution,[],[f93,f46])).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f22])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.19/0.54  fof(f128,plain,(
% 0.19/0.54    spl9_8 | ~spl9_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f112,f91,f125])).
% 0.19/0.54  fof(f112,plain,(
% 0.19/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl9_3),
% 0.19/0.54    inference(resolution,[],[f93,f66])).
% 0.19/0.54  fof(f66,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f11])).
% 0.19/0.54  fof(f103,plain,(
% 0.19/0.54    ~spl9_4 | spl9_5),
% 0.19/0.54    inference(avatar_split_clause,[],[f36,f100,f96])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f94,plain,(
% 0.19/0.54    spl9_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f40,f91])).
% 0.19/0.54  fof(f40,plain,(
% 0.19/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f89,plain,(
% 0.19/0.54    spl9_2),
% 0.19/0.54    inference(avatar_split_clause,[],[f42,f86])).
% 0.19/0.54  fof(f42,plain,(
% 0.19/0.54    l1_pre_topc(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f84,plain,(
% 0.19/0.54    spl9_1),
% 0.19/0.54    inference(avatar_split_clause,[],[f41,f81])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    v2_pre_topc(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (21058)------------------------------
% 0.19/0.54  % (21058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (21058)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (21058)Memory used [KB]: 11001
% 0.19/0.54  % (21058)Time elapsed: 0.128 s
% 0.19/0.54  % (21058)------------------------------
% 0.19/0.54  % (21058)------------------------------
% 0.19/0.54  % (21035)Success in time 0.2 s
%------------------------------------------------------------------------------
