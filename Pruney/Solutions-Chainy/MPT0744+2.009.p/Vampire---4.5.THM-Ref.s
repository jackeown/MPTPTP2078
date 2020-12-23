%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:30 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 121 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 ( 341 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f112,f170,f253])).

fof(f253,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f50,f206,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f206,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f87,f194])).

fof(f194,plain,
    ( sK0 = sK1
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f26,f27,f86,f185,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

% (4139)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (4118)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (4129)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (4128)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (4147)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (4131)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (4146)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (4119)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (4147)Refutation not found, incomplete strategy% (4147)------------------------------
% (4147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4147)Termination reason: Refutation not found, incomplete strategy

% (4147)Memory used [KB]: 1663
% (4147)Time elapsed: 0.092 s
% (4147)------------------------------
% (4147)------------------------------
% (4146)Refutation not found, incomplete strategy% (4146)------------------------------
% (4146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4146)Termination reason: Refutation not found, incomplete strategy

% (4146)Memory used [KB]: 10746
% (4146)Time elapsed: 0.130 s
% (4146)------------------------------
% (4146)------------------------------
% (4120)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (4145)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (4135)Refutation not found, incomplete strategy% (4135)------------------------------
% (4135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4135)Termination reason: Refutation not found, incomplete strategy

% (4135)Memory used [KB]: 1663
% (4135)Time elapsed: 0.115 s
% (4135)------------------------------
% (4135)------------------------------
% (4137)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (4141)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (4130)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f185,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f171,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f171,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f27,f26,f83,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f83,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f80,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f170,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f120,f135,f32])).

fof(f135,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f122,f79,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f79,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f122,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f114,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f114,plain,
    ( r2_hidden(sK1,sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f26,f27,f84,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f84,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f120,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f114,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f112,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f48,f82,f78])).

fof(f48,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f35,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f24,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f82,f78])).

fof(f47,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f25,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (4136)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (4122)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (4121)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (4144)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (4135)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (4126)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (4127)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (4124)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (4143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (4138)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.52  % (4125)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.52  % (4143)Refutation found. Thanks to Tanya!
% 1.31/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.52  fof(f254,plain,(
% 1.31/0.52    $false),
% 1.31/0.52    inference(avatar_sat_refutation,[],[f85,f112,f170,f253])).
% 1.31/0.52  fof(f253,plain,(
% 1.31/0.52    spl3_1 | ~spl3_2),
% 1.31/0.52    inference(avatar_contradiction_clause,[],[f252])).
% 1.31/0.52  fof(f252,plain,(
% 1.31/0.52    $false | (spl3_1 | ~spl3_2)),
% 1.31/0.52    inference(unit_resulting_resolution,[],[f50,f206,f37])).
% 1.31/0.52  fof(f37,plain,(
% 1.31/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f4])).
% 1.31/0.52  fof(f4,axiom,(
% 1.31/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.31/0.52  fof(f206,plain,(
% 1.31/0.52    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl3_1 | ~spl3_2)),
% 1.31/0.52    inference(backward_demodulation,[],[f87,f194])).
% 1.31/0.52  fof(f194,plain,(
% 1.31/0.52    sK0 = sK1 | (spl3_1 | ~spl3_2)),
% 1.31/0.52    inference(unit_resulting_resolution,[],[f26,f27,f86,f185,f34])).
% 1.31/0.52  fof(f34,plain,(
% 1.31/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f23])).
% 1.31/0.53  % (4139)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.53  % (4118)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.53  % (4129)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.53  % (4128)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.53  % (4147)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.53  % (4131)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.53  % (4146)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.54  % (4119)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.54  % (4147)Refutation not found, incomplete strategy% (4147)------------------------------
% 1.31/0.54  % (4147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (4147)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (4147)Memory used [KB]: 1663
% 1.31/0.54  % (4147)Time elapsed: 0.092 s
% 1.31/0.54  % (4147)------------------------------
% 1.31/0.54  % (4147)------------------------------
% 1.31/0.54  % (4146)Refutation not found, incomplete strategy% (4146)------------------------------
% 1.31/0.54  % (4146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (4146)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (4146)Memory used [KB]: 10746
% 1.31/0.54  % (4146)Time elapsed: 0.130 s
% 1.31/0.54  % (4146)------------------------------
% 1.31/0.54  % (4146)------------------------------
% 1.31/0.54  % (4120)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.54  % (4145)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  % (4135)Refutation not found, incomplete strategy% (4135)------------------------------
% 1.31/0.54  % (4135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (4135)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (4135)Memory used [KB]: 1663
% 1.31/0.54  % (4135)Time elapsed: 0.115 s
% 1.31/0.54  % (4135)------------------------------
% 1.31/0.54  % (4135)------------------------------
% 1.31/0.54  % (4137)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.54  % (4141)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(flattening,[],[f22])).
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f8])).
% 1.43/0.54  % (4130)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.54  fof(f8,axiom,(
% 1.43/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.43/0.54  fof(f185,plain,(
% 1.43/0.54    ~r2_hidden(sK1,sK0) | ~spl3_2),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f171,f32])).
% 1.43/0.54  fof(f32,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f20])).
% 1.43/0.54  fof(f20,plain,(
% 1.43/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.43/0.54    inference(ennf_transformation,[],[f10])).
% 1.43/0.54  fof(f10,axiom,(
% 1.43/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.43/0.54  fof(f171,plain,(
% 1.43/0.54    r1_tarski(sK0,sK1) | ~spl3_2),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f27,f26,f83,f29])).
% 1.43/0.54  fof(f29,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f15,plain,(
% 1.43/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(flattening,[],[f14])).
% 1.43/0.54  fof(f14,plain,(
% 1.43/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f7])).
% 1.43/0.54  fof(f7,axiom,(
% 1.43/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.43/0.54  fof(f83,plain,(
% 1.43/0.54    r1_ordinal1(sK0,sK1) | ~spl3_2),
% 1.43/0.54    inference(avatar_component_clause,[],[f82])).
% 1.43/0.54  fof(f82,plain,(
% 1.43/0.54    spl3_2 <=> r1_ordinal1(sK0,sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.43/0.54  fof(f86,plain,(
% 1.43/0.54    ~r2_hidden(sK0,sK1) | spl3_1),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f80,f52])).
% 1.43/0.54  fof(f52,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(equality_resolution,[],[f45])).
% 1.43/0.54  fof(f45,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f2,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.43/0.54  fof(f80,plain,(
% 1.43/0.54    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl3_1),
% 1.43/0.54    inference(avatar_component_clause,[],[f78])).
% 1.43/0.54  fof(f78,plain,(
% 1.43/0.54    spl3_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.43/0.54  fof(f27,plain,(
% 1.43/0.54    v3_ordinal1(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f13])).
% 1.43/0.54  fof(f13,plain,(
% 1.43/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f12])).
% 1.43/0.54  fof(f12,negated_conjecture,(
% 1.43/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.43/0.54    inference(negated_conjecture,[],[f11])).
% 1.43/0.54  fof(f11,conjecture,(
% 1.43/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.43/0.54  fof(f26,plain,(
% 1.43/0.54    v3_ordinal1(sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f13])).
% 1.43/0.54  fof(f87,plain,(
% 1.43/0.54    ~r2_hidden(sK0,k1_tarski(sK1)) | spl3_1),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f80,f51])).
% 1.43/0.54  fof(f51,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(equality_resolution,[],[f46])).
% 1.43/0.54  fof(f46,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f50,plain,(
% 1.43/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.54    inference(equality_resolution,[],[f38])).
% 1.43/0.54  fof(f38,plain,(
% 1.43/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.54  fof(f170,plain,(
% 1.43/0.54    ~spl3_1 | spl3_2),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f165])).
% 1.43/0.54  fof(f165,plain,(
% 1.43/0.54    $false | (~spl3_1 | spl3_2)),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f120,f135,f32])).
% 1.43/0.54  fof(f135,plain,(
% 1.43/0.54    r2_hidden(sK0,k1_tarski(sK1)) | (~spl3_1 | spl3_2)),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f122,f79,f53])).
% 1.43/0.54  fof(f53,plain,(
% 1.43/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.43/0.54    inference(equality_resolution,[],[f44])).
% 1.43/0.54  fof(f44,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f79,plain,(
% 1.43/0.54    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl3_1),
% 1.43/0.54    inference(avatar_component_clause,[],[f78])).
% 1.43/0.54  fof(f122,plain,(
% 1.43/0.54    ~r2_hidden(sK0,sK1) | spl3_2),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f114,f33])).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f21])).
% 1.43/0.54  fof(f21,plain,(
% 1.43/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.43/0.54    inference(ennf_transformation,[],[f1])).
% 1.43/0.54  fof(f1,axiom,(
% 1.43/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.43/0.54  fof(f114,plain,(
% 1.43/0.54    r2_hidden(sK1,sK0) | spl3_2),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f26,f27,f84,f31])).
% 1.43/0.54  fof(f31,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f19])).
% 1.43/0.54  fof(f19,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(flattening,[],[f18])).
% 1.43/0.54  fof(f18,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f9])).
% 1.43/0.54  fof(f9,axiom,(
% 1.43/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.43/0.54  fof(f84,plain,(
% 1.43/0.54    ~r1_ordinal1(sK0,sK1) | spl3_2),
% 1.43/0.54    inference(avatar_component_clause,[],[f82])).
% 1.43/0.54  fof(f120,plain,(
% 1.43/0.54    r1_tarski(k1_tarski(sK1),sK0) | spl3_2),
% 1.43/0.54    inference(unit_resulting_resolution,[],[f114,f36])).
% 1.43/0.54  fof(f36,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f4])).
% 1.43/0.54  fof(f112,plain,(
% 1.43/0.54    spl3_1 | spl3_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f48,f82,f78])).
% 1.43/0.54  fof(f48,plain,(
% 1.43/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.43/0.54    inference(definition_unfolding,[],[f24,f35])).
% 1.43/0.54  fof(f35,plain,(
% 1.43/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f6])).
% 1.43/0.54  fof(f6,axiom,(
% 1.43/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.43/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.43/0.54  fof(f24,plain,(
% 1.43/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.43/0.54    inference(cnf_transformation,[],[f13])).
% 1.43/0.54  fof(f85,plain,(
% 1.43/0.54    ~spl3_1 | ~spl3_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f47,f82,f78])).
% 1.43/0.54  fof(f47,plain,(
% 1.43/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.43/0.54    inference(definition_unfolding,[],[f25,f35])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.43/0.54    inference(cnf_transformation,[],[f13])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (4143)------------------------------
% 1.43/0.54  % (4143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (4143)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (4143)Memory used [KB]: 6268
% 1.43/0.54  % (4143)Time elapsed: 0.126 s
% 1.43/0.54  % (4143)------------------------------
% 1.43/0.54  % (4143)------------------------------
% 1.43/0.54  % (4117)Success in time 0.181 s
%------------------------------------------------------------------------------
