%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:35 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 243 expanded)
%              Number of leaves         :   24 (  94 expanded)
%              Depth                    :    8
%              Number of atoms          :  314 ( 652 expanded)
%              Number of equality atoms :   56 ( 170 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f73,f78,f100,f133,f164,f176,f183,f213,f262,f294,f300,f307,f321,f354,f408,f454,f463])).

fof(f463,plain,
    ( spl11_19
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f462,f452,f297])).

fof(f297,plain,
    ( spl11_19
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f452,plain,
    ( spl11_24
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f462,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl11_24 ),
    inference(duplicate_literal_removal,[],[f459])).

fof(f459,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl11_24 ),
    inference(resolution,[],[f456,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f456,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(X1,sK1),sK3)
        | r1_tarski(X1,sK1) )
    | ~ spl11_24 ),
    inference(resolution,[],[f453,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f453,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,sK3) )
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f452])).

fof(f454,plain,
    ( spl11_24
    | spl11_14
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f443,f75,f70,f178,f452])).

fof(f178,plain,
    ( spl11_14
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f70,plain,
    ( spl11_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

% (6718)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (6732)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (6733)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (6722)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (6720)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (6731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (6736)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (6725)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (6723)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f75,plain,
    ( spl11_5
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f443,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,sK0)
        | ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) )
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f168,f71])).

fof(f71,plain,
    ( sK0 = sK2
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f168,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X7,sK2)
        | r2_hidden(X6,sK1) )
    | ~ spl11_5 ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f81,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    | ~ spl11_5 ),
    inference(superposition,[],[f46,f77])).

fof(f77,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f408,plain,
    ( ~ spl11_3
    | spl11_10
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl11_3
    | spl11_10
    | ~ spl11_21 ),
    inference(unit_resulting_resolution,[],[f145,f373,f395,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f395,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_3
    | ~ spl11_21 ),
    inference(superposition,[],[f378,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f378,plain,
    ( ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(sK1,X5))
    | ~ spl11_3
    | ~ spl11_21 ),
    inference(resolution,[],[f373,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f373,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl11_3
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f306,f67])).

fof(f67,plain,
    ( sK1 = sK3
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl11_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f306,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl11_21
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f145,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_10
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f354,plain,
    ( spl11_19
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl11_19
    | ~ spl11_21 ),
    inference(unit_resulting_resolution,[],[f299,f306,f22])).

fof(f299,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl11_19 ),
    inference(avatar_component_clause,[],[f297])).

fof(f321,plain,
    ( spl11_13
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f320,f302,f173])).

fof(f173,plain,
    ( spl11_13
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f302,plain,
    ( spl11_20
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f320,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl11_20 ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl11_20 ),
    inference(resolution,[],[f314,f22])).

fof(f314,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(X1,sK0),sK2)
        | r1_tarski(X1,sK0) )
    | ~ spl11_20 ),
    inference(resolution,[],[f303,f23])).

fof(f303,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f302])).

fof(f307,plain,
    ( spl11_20
    | spl11_21
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f167,f75,f305,f302])).

fof(f167,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl11_5 ),
    inference(resolution,[],[f81,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f300,plain,
    ( ~ spl11_19
    | spl11_3
    | spl11_18 ),
    inference(avatar_split_clause,[],[f295,f291,f66,f297])).

fof(f291,plain,
    ( spl11_18
  <=> r2_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f295,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK3,sK1)
    | spl11_18 ),
    inference(resolution,[],[f293,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f293,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | spl11_18 ),
    inference(avatar_component_clause,[],[f291])).

fof(f294,plain,
    ( ~ spl11_18
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f289,f181,f291])).

fof(f181,plain,
    ( spl11_15
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f289,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | ~ spl11_15 ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | ~ r2_xboole_0(sK3,sK1)
    | ~ spl11_15 ),
    inference(resolution,[],[f272,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f272,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK3,X1),sK1)
        | ~ r2_xboole_0(sK3,X1) )
    | ~ spl11_15 ),
    inference(resolution,[],[f182,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f262,plain,
    ( spl11_1
    | spl11_2
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl11_1
    | spl11_2
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f58,f63,f144,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f144,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | spl11_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f58,plain,
    ( k1_xboole_0 != sK0
    | spl11_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl11_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f213,plain,
    ( spl11_10
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl11_10
    | ~ spl11_14 ),
    inference(unit_resulting_resolution,[],[f145,f179,f202,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f202,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_14 ),
    inference(superposition,[],[f187,f48])).

fof(f187,plain,
    ( ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(sK0,X5))
    | ~ spl11_14 ),
    inference(resolution,[],[f179,f54])).

fof(f179,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f183,plain,
    ( spl11_14
    | spl11_15
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f89,f75,f181,f178])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl11_5 ),
    inference(resolution,[],[f80,f46])).

fof(f80,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK3) )
    | ~ spl11_5 ),
    inference(superposition,[],[f45,f77])).

fof(f176,plain,
    ( ~ spl11_13
    | spl11_4
    | spl11_12 ),
    inference(avatar_split_clause,[],[f171,f161,f70,f173])).

fof(f161,plain,
    ( spl11_12
  <=> r2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f171,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK2,sK0)
    | spl11_12 ),
    inference(resolution,[],[f163,f26])).

fof(f163,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( ~ spl11_12
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f159,f98,f161])).

fof(f98,plain,
    ( spl11_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f159,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | ~ spl11_7 ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | ~ r2_xboole_0(sK2,sK0)
    | ~ spl11_7 ),
    inference(resolution,[],[f148,f30])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK2,X1),sK0)
        | ~ r2_xboole_0(sK2,X1) )
    | ~ spl11_7 ),
    inference(resolution,[],[f99,f31])).

fof(f99,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f133,plain,
    ( spl11_2
    | ~ spl11_6 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl11_2
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f103,f63,f122,f26])).

fof(f122,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl11_6 ),
    inference(resolution,[],[f118,f22])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_6 ),
    inference(superposition,[],[f104,f48])).

fof(f104,plain,
    ( ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(sK1,X5))
    | ~ spl11_6 ),
    inference(resolution,[],[f96,f54])).

fof(f96,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl11_6
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f103,plain,
    ( ! [X3] : ~ r2_xboole_0(X3,sK1)
    | ~ spl11_6 ),
    inference(resolution,[],[f96,f30])).

fof(f100,plain,
    ( spl11_6
    | spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f84,f75,f98,f95])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_5 ),
    inference(resolution,[],[f79,f46])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl11_5 ),
    inference(superposition,[],[f44,f77])).

fof(f78,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f17,f75])).

fof(f17,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f73,plain,
    ( ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f16,f70,f66])).

fof(f16,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ~ spl11_2 ),
    inference(avatar_split_clause,[],[f19,f61])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f18,f56])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:59:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (6721)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.52  % (6737)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.52  % (6716)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (6729)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.54  % (6734)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.54  % (6712)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (6712)Refutation not found, incomplete strategy% (6712)------------------------------
% 0.23/0.54  % (6712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (6712)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (6712)Memory used [KB]: 1663
% 0.23/0.54  % (6712)Time elapsed: 0.090 s
% 0.23/0.54  % (6712)------------------------------
% 0.23/0.54  % (6712)------------------------------
% 0.23/0.54  % (6727)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.54  % (6729)Refutation not found, incomplete strategy% (6729)------------------------------
% 0.23/0.54  % (6729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (6729)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (6729)Memory used [KB]: 10618
% 0.23/0.54  % (6729)Time elapsed: 0.113 s
% 0.23/0.54  % (6729)------------------------------
% 0.23/0.54  % (6729)------------------------------
% 0.23/0.54  % (6726)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.55  % (6738)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (6724)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (6735)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.55  % (6717)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.55  % (6715)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.55  % (6713)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.55  % (6714)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.55  % (6740)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.56  % (6719)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.56  % (6741)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.56  % (6728)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.56  % (6730)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.56  % (6739)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.56  % (6734)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f464,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(avatar_sat_refutation,[],[f59,f64,f73,f78,f100,f133,f164,f176,f183,f213,f262,f294,f300,f307,f321,f354,f408,f454,f463])).
% 1.34/0.56  fof(f463,plain,(
% 1.34/0.56    spl11_19 | ~spl11_24),
% 1.34/0.56    inference(avatar_split_clause,[],[f462,f452,f297])).
% 1.34/0.56  fof(f297,plain,(
% 1.34/0.56    spl11_19 <=> r1_tarski(sK3,sK1)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 1.34/0.56  fof(f452,plain,(
% 1.34/0.56    spl11_24 <=> ! [X6] : (~r2_hidden(X6,sK3) | r2_hidden(X6,sK1))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 1.34/0.56  fof(f462,plain,(
% 1.34/0.56    r1_tarski(sK3,sK1) | ~spl11_24),
% 1.34/0.56    inference(duplicate_literal_removal,[],[f459])).
% 1.34/0.56  fof(f459,plain,(
% 1.34/0.56    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl11_24),
% 1.34/0.56    inference(resolution,[],[f456,f22])).
% 1.34/0.56  fof(f22,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f13])).
% 1.34/0.56  fof(f13,plain,(
% 1.34/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.56    inference(ennf_transformation,[],[f1])).
% 1.34/0.56  fof(f1,axiom,(
% 1.34/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.56  fof(f456,plain,(
% 1.34/0.56    ( ! [X1] : (~r2_hidden(sK4(X1,sK1),sK3) | r1_tarski(X1,sK1)) ) | ~spl11_24),
% 1.34/0.56    inference(resolution,[],[f453,f23])).
% 1.34/0.56  fof(f23,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f13])).
% 1.34/0.56  fof(f453,plain,(
% 1.34/0.56    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,sK3)) ) | ~spl11_24),
% 1.34/0.56    inference(avatar_component_clause,[],[f452])).
% 1.34/0.56  fof(f454,plain,(
% 1.34/0.56    spl11_24 | spl11_14 | ~spl11_4 | ~spl11_5),
% 1.34/0.56    inference(avatar_split_clause,[],[f443,f75,f70,f178,f452])).
% 1.34/0.56  fof(f178,plain,(
% 1.34/0.56    spl11_14 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.34/0.56  fof(f70,plain,(
% 1.34/0.56    spl11_4 <=> sK0 = sK2),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.34/0.56  % (6718)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.56  % (6732)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.56  % (6733)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.56  % (6722)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.56  % (6720)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.56  % (6731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (6736)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.57  % (6725)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.57  % (6723)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.58  fof(f75,plain,(
% 1.54/0.58    spl11_5 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.54/0.58  fof(f443,plain,(
% 1.54/0.58    ( ! [X6,X7] : (~r2_hidden(X7,sK0) | ~r2_hidden(X6,sK3) | r2_hidden(X6,sK1)) ) | (~spl11_4 | ~spl11_5)),
% 1.54/0.58    inference(forward_demodulation,[],[f168,f71])).
% 1.54/0.58  fof(f71,plain,(
% 1.54/0.58    sK0 = sK2 | ~spl11_4),
% 1.54/0.58    inference(avatar_component_clause,[],[f70])).
% 1.54/0.58  fof(f168,plain,(
% 1.54/0.58    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X6,sK1)) ) | ~spl11_5),
% 1.54/0.58    inference(resolution,[],[f81,f45])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.54/0.58  fof(f81,plain,(
% 1.54/0.58    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) ) | ~spl11_5),
% 1.54/0.58    inference(superposition,[],[f46,f77])).
% 1.54/0.58  fof(f77,plain,(
% 1.54/0.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~spl11_5),
% 1.54/0.58    inference(avatar_component_clause,[],[f75])).
% 1.54/0.58  fof(f46,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f408,plain,(
% 1.54/0.58    ~spl11_3 | spl11_10 | ~spl11_21),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f399])).
% 1.54/0.58  fof(f399,plain,(
% 1.54/0.58    $false | (~spl11_3 | spl11_10 | ~spl11_21)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f145,f373,f395,f34])).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.54/0.58  fof(f395,plain,(
% 1.54/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl11_3 | ~spl11_21)),
% 1.54/0.58    inference(superposition,[],[f378,f48])).
% 1.54/0.58  fof(f48,plain,(
% 1.54/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.54/0.58    inference(equality_resolution,[],[f29])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.54/0.58  fof(f378,plain,(
% 1.54/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(sK1,X5))) ) | (~spl11_3 | ~spl11_21)),
% 1.54/0.58    inference(resolution,[],[f373,f54])).
% 1.54/0.58  fof(f54,plain,(
% 1.54/0.58    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.54/0.58    inference(equality_resolution,[],[f36])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f373,plain,(
% 1.54/0.58    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | (~spl11_3 | ~spl11_21)),
% 1.54/0.58    inference(forward_demodulation,[],[f306,f67])).
% 1.54/0.58  fof(f67,plain,(
% 1.54/0.58    sK1 = sK3 | ~spl11_3),
% 1.54/0.58    inference(avatar_component_clause,[],[f66])).
% 1.54/0.58  fof(f66,plain,(
% 1.54/0.58    spl11_3 <=> sK1 = sK3),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.54/0.58  fof(f306,plain,(
% 1.54/0.58    ( ! [X4] : (~r2_hidden(X4,sK3)) ) | ~spl11_21),
% 1.54/0.58    inference(avatar_component_clause,[],[f305])).
% 1.54/0.58  fof(f305,plain,(
% 1.54/0.58    spl11_21 <=> ! [X4] : ~r2_hidden(X4,sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.54/0.58  fof(f145,plain,(
% 1.54/0.58    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl11_10),
% 1.54/0.58    inference(avatar_component_clause,[],[f143])).
% 1.54/0.58  fof(f143,plain,(
% 1.54/0.58    spl11_10 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.54/0.58  fof(f354,plain,(
% 1.54/0.58    spl11_19 | ~spl11_21),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f345])).
% 1.54/0.58  fof(f345,plain,(
% 1.54/0.58    $false | (spl11_19 | ~spl11_21)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f299,f306,f22])).
% 1.54/0.58  fof(f299,plain,(
% 1.54/0.58    ~r1_tarski(sK3,sK1) | spl11_19),
% 1.54/0.58    inference(avatar_component_clause,[],[f297])).
% 1.54/0.58  fof(f321,plain,(
% 1.54/0.58    spl11_13 | ~spl11_20),
% 1.54/0.58    inference(avatar_split_clause,[],[f320,f302,f173])).
% 1.54/0.58  fof(f173,plain,(
% 1.54/0.58    spl11_13 <=> r1_tarski(sK2,sK0)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.54/0.58  fof(f302,plain,(
% 1.54/0.58    spl11_20 <=> ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 1.54/0.58  fof(f320,plain,(
% 1.54/0.58    r1_tarski(sK2,sK0) | ~spl11_20),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f317])).
% 1.54/0.58  fof(f317,plain,(
% 1.54/0.58    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl11_20),
% 1.54/0.58    inference(resolution,[],[f314,f22])).
% 1.54/0.58  fof(f314,plain,(
% 1.54/0.58    ( ! [X1] : (~r2_hidden(sK4(X1,sK0),sK2) | r1_tarski(X1,sK0)) ) | ~spl11_20),
% 1.54/0.58    inference(resolution,[],[f303,f23])).
% 1.54/0.58  fof(f303,plain,(
% 1.54/0.58    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2)) ) | ~spl11_20),
% 1.54/0.58    inference(avatar_component_clause,[],[f302])).
% 1.54/0.58  fof(f307,plain,(
% 1.54/0.58    spl11_20 | spl11_21 | ~spl11_5),
% 1.54/0.58    inference(avatar_split_clause,[],[f167,f75,f305,f302])).
% 1.54/0.58  fof(f167,plain,(
% 1.54/0.58    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) ) | ~spl11_5),
% 1.54/0.58    inference(resolution,[],[f81,f44])).
% 1.54/0.58  fof(f44,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f300,plain,(
% 1.54/0.58    ~spl11_19 | spl11_3 | spl11_18),
% 1.54/0.58    inference(avatar_split_clause,[],[f295,f291,f66,f297])).
% 1.54/0.58  fof(f291,plain,(
% 1.54/0.58    spl11_18 <=> r2_xboole_0(sK3,sK1)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.54/0.58  fof(f295,plain,(
% 1.54/0.58    sK1 = sK3 | ~r1_tarski(sK3,sK1) | spl11_18),
% 1.54/0.58    inference(resolution,[],[f293,f26])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.54/0.58  fof(f293,plain,(
% 1.54/0.58    ~r2_xboole_0(sK3,sK1) | spl11_18),
% 1.54/0.58    inference(avatar_component_clause,[],[f291])).
% 1.54/0.58  fof(f294,plain,(
% 1.54/0.58    ~spl11_18 | ~spl11_15),
% 1.54/0.58    inference(avatar_split_clause,[],[f289,f181,f291])).
% 1.54/0.58  fof(f181,plain,(
% 1.54/0.58    spl11_15 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 1.54/0.58  fof(f289,plain,(
% 1.54/0.58    ~r2_xboole_0(sK3,sK1) | ~spl11_15),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f287])).
% 1.54/0.58  fof(f287,plain,(
% 1.54/0.58    ~r2_xboole_0(sK3,sK1) | ~r2_xboole_0(sK3,sK1) | ~spl11_15),
% 1.54/0.58    inference(resolution,[],[f272,f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f14,plain,(
% 1.54/0.58    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.54/0.58  fof(f272,plain,(
% 1.54/0.58    ( ! [X1] : (~r2_hidden(sK5(sK3,X1),sK1) | ~r2_xboole_0(sK3,X1)) ) | ~spl11_15),
% 1.54/0.58    inference(resolution,[],[f182,f31])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f182,plain,(
% 1.54/0.58    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl11_15),
% 1.54/0.58    inference(avatar_component_clause,[],[f181])).
% 1.54/0.58  fof(f262,plain,(
% 1.54/0.58    spl11_1 | spl11_2 | ~spl11_10),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f255])).
% 1.54/0.58  fof(f255,plain,(
% 1.54/0.58    $false | (spl11_1 | spl11_2 | ~spl11_10)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f58,f63,f144,f27])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f144,plain,(
% 1.54/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_10),
% 1.54/0.58    inference(avatar_component_clause,[],[f143])).
% 1.54/0.58  fof(f63,plain,(
% 1.54/0.58    k1_xboole_0 != sK1 | spl11_2),
% 1.54/0.58    inference(avatar_component_clause,[],[f61])).
% 1.54/0.58  fof(f61,plain,(
% 1.54/0.58    spl11_2 <=> k1_xboole_0 = sK1),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.54/0.58  fof(f58,plain,(
% 1.54/0.58    k1_xboole_0 != sK0 | spl11_1),
% 1.54/0.58    inference(avatar_component_clause,[],[f56])).
% 1.54/0.58  fof(f56,plain,(
% 1.54/0.58    spl11_1 <=> k1_xboole_0 = sK0),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.54/0.58  fof(f213,plain,(
% 1.54/0.58    spl11_10 | ~spl11_14),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f205])).
% 1.54/0.58  fof(f205,plain,(
% 1.54/0.58    $false | (spl11_10 | ~spl11_14)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f145,f179,f202,f33])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f202,plain,(
% 1.54/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl11_14),
% 1.54/0.58    inference(superposition,[],[f187,f48])).
% 1.54/0.58  fof(f187,plain,(
% 1.54/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(sK0,X5))) ) | ~spl11_14),
% 1.54/0.58    inference(resolution,[],[f179,f54])).
% 1.54/0.58  fof(f179,plain,(
% 1.54/0.58    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl11_14),
% 1.54/0.58    inference(avatar_component_clause,[],[f178])).
% 1.54/0.58  fof(f183,plain,(
% 1.54/0.58    spl11_14 | spl11_15 | ~spl11_5),
% 1.54/0.58    inference(avatar_split_clause,[],[f89,f75,f181,f178])).
% 1.54/0.58  fof(f89,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl11_5),
% 1.54/0.58    inference(resolution,[],[f80,f46])).
% 1.54/0.58  fof(f80,plain,(
% 1.54/0.58    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) ) | ~spl11_5),
% 1.54/0.58    inference(superposition,[],[f45,f77])).
% 1.54/0.58  fof(f176,plain,(
% 1.54/0.58    ~spl11_13 | spl11_4 | spl11_12),
% 1.54/0.58    inference(avatar_split_clause,[],[f171,f161,f70,f173])).
% 1.54/0.58  fof(f161,plain,(
% 1.54/0.58    spl11_12 <=> r2_xboole_0(sK2,sK0)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.54/0.58  fof(f171,plain,(
% 1.54/0.58    sK0 = sK2 | ~r1_tarski(sK2,sK0) | spl11_12),
% 1.54/0.58    inference(resolution,[],[f163,f26])).
% 1.54/0.58  fof(f163,plain,(
% 1.54/0.58    ~r2_xboole_0(sK2,sK0) | spl11_12),
% 1.54/0.58    inference(avatar_component_clause,[],[f161])).
% 1.54/0.58  fof(f164,plain,(
% 1.54/0.58    ~spl11_12 | ~spl11_7),
% 1.54/0.58    inference(avatar_split_clause,[],[f159,f98,f161])).
% 1.54/0.58  fof(f98,plain,(
% 1.54/0.58    spl11_7 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.54/0.58  fof(f159,plain,(
% 1.54/0.58    ~r2_xboole_0(sK2,sK0) | ~spl11_7),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f157])).
% 1.54/0.58  fof(f157,plain,(
% 1.54/0.58    ~r2_xboole_0(sK2,sK0) | ~r2_xboole_0(sK2,sK0) | ~spl11_7),
% 1.54/0.58    inference(resolution,[],[f148,f30])).
% 1.54/0.58  fof(f148,plain,(
% 1.54/0.58    ( ! [X1] : (~r2_hidden(sK5(sK2,X1),sK0) | ~r2_xboole_0(sK2,X1)) ) | ~spl11_7),
% 1.54/0.58    inference(resolution,[],[f99,f31])).
% 1.54/0.58  fof(f99,plain,(
% 1.54/0.58    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl11_7),
% 1.54/0.58    inference(avatar_component_clause,[],[f98])).
% 1.54/0.58  fof(f133,plain,(
% 1.54/0.58    spl11_2 | ~spl11_6),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f132])).
% 1.54/0.58  fof(f132,plain,(
% 1.54/0.58    $false | (spl11_2 | ~spl11_6)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f103,f63,f122,f26])).
% 1.54/0.58  fof(f122,plain,(
% 1.54/0.58    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl11_6),
% 1.54/0.58    inference(resolution,[],[f118,f22])).
% 1.54/0.58  fof(f118,plain,(
% 1.54/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl11_6),
% 1.54/0.58    inference(superposition,[],[f104,f48])).
% 1.54/0.58  fof(f104,plain,(
% 1.54/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(sK1,X5))) ) | ~spl11_6),
% 1.54/0.58    inference(resolution,[],[f96,f54])).
% 1.54/0.58  fof(f96,plain,(
% 1.54/0.58    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl11_6),
% 1.54/0.58    inference(avatar_component_clause,[],[f95])).
% 1.54/0.58  fof(f95,plain,(
% 1.54/0.58    spl11_6 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.54/0.58  fof(f103,plain,(
% 1.54/0.58    ( ! [X3] : (~r2_xboole_0(X3,sK1)) ) | ~spl11_6),
% 1.54/0.58    inference(resolution,[],[f96,f30])).
% 1.54/0.58  fof(f100,plain,(
% 1.54/0.58    spl11_6 | spl11_7 | ~spl11_5),
% 1.54/0.58    inference(avatar_split_clause,[],[f84,f75,f98,f95])).
% 1.54/0.58  fof(f84,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl11_5),
% 1.54/0.58    inference(resolution,[],[f79,f46])).
% 1.54/0.58  fof(f79,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) ) | ~spl11_5),
% 1.54/0.58    inference(superposition,[],[f44,f77])).
% 1.54/0.58  fof(f78,plain,(
% 1.54/0.58    spl11_5),
% 1.54/0.58    inference(avatar_split_clause,[],[f17,f75])).
% 1.54/0.58  fof(f17,plain,(
% 1.54/0.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 1.54/0.58    inference(cnf_transformation,[],[f12])).
% 1.54/0.58  fof(f12,plain,(
% 1.54/0.58    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.54/0.58    inference(flattening,[],[f11])).
% 1.54/0.58  fof(f11,plain,(
% 1.54/0.58    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.54/0.58    inference(ennf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.54/0.58    inference(negated_conjecture,[],[f9])).
% 1.54/0.58  fof(f9,conjecture,(
% 1.54/0.58    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.54/0.58  fof(f73,plain,(
% 1.54/0.58    ~spl11_3 | ~spl11_4),
% 1.54/0.58    inference(avatar_split_clause,[],[f16,f70,f66])).
% 1.54/0.58  fof(f16,plain,(
% 1.54/0.58    sK0 != sK2 | sK1 != sK3),
% 1.54/0.58    inference(cnf_transformation,[],[f12])).
% 1.54/0.58  fof(f64,plain,(
% 1.54/0.58    ~spl11_2),
% 1.54/0.58    inference(avatar_split_clause,[],[f19,f61])).
% 1.54/0.58  fof(f19,plain,(
% 1.54/0.58    k1_xboole_0 != sK1),
% 1.54/0.58    inference(cnf_transformation,[],[f12])).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    ~spl11_1),
% 1.54/0.58    inference(avatar_split_clause,[],[f18,f56])).
% 1.54/0.58  fof(f18,plain,(
% 1.54/0.58    k1_xboole_0 != sK0),
% 1.54/0.58    inference(cnf_transformation,[],[f12])).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (6734)------------------------------
% 1.54/0.58  % (6734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (6734)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (6734)Memory used [KB]: 10874
% 1.54/0.58  % (6734)Time elapsed: 0.096 s
% 1.54/0.58  % (6734)------------------------------
% 1.54/0.58  % (6734)------------------------------
% 1.54/0.58  % (6711)Success in time 0.208 s
%------------------------------------------------------------------------------
