%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 129 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 ( 304 expanded)
%              Number of equality atoms :   23 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f81,f142,f156,f173,f198])).

fof(f198,plain,
    ( spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f42,f137,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f137,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_4
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f42,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl8_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f173,plain,
    ( ~ spl8_1
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f141,f141,f102])).

fof(f102,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,X3) )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f96,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f96,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f93,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK1(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f93,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k1_xboole_0)
        | ~ r2_hidden(X4,X5) )
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X4,X5)
        | ~ r2_hidden(k4_tarski(X3,X4),k1_xboole_0)
        | ~ r2_hidden(X4,X5) )
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f91,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f91,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k1_xboole_0)
        | ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X4,k5_xboole_0(X5,k1_xboole_0)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f85,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f85,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X2,X1),k1_xboole_0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f34,f37])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f141,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_5
  <=> r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f156,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f143,f143,f102])).

fof(f143,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f134,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f134,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f142,plain,
    ( ~ spl8_3
    | spl8_4
    | spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f84,f36,f139,f136,f132])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f22,f37])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f81,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f44,f63,f33])).

fof(f63,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | spl8_1 ),
    inference(forward_demodulation,[],[f60,f25])).

fof(f60,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f45,f45,f30])).

fof(f45,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f44,f33])).

fof(f44,plain,
    ( r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f38,f24])).

fof(f38,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f43,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f17,f40,f36])).

fof(f17,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:14:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5050)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (5050)Refutation not found, incomplete strategy% (5050)------------------------------
% 0.21/0.51  % (5050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5066)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (5050)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5050)Memory used [KB]: 10618
% 0.21/0.51  % (5050)Time elapsed: 0.093 s
% 0.21/0.51  % (5050)------------------------------
% 0.21/0.51  % (5050)------------------------------
% 0.21/0.51  % (5058)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (5071)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (5058)Refutation not found, incomplete strategy% (5058)------------------------------
% 0.21/0.52  % (5058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5058)Memory used [KB]: 10618
% 0.21/0.52  % (5058)Time elapsed: 0.110 s
% 0.21/0.52  % (5058)------------------------------
% 0.21/0.52  % (5058)------------------------------
% 0.21/0.52  % (5061)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (5051)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (5054)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (5055)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (5049)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5077)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (5048)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (5048)Refutation not found, incomplete strategy% (5048)------------------------------
% 0.21/0.53  % (5048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5048)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5048)Memory used [KB]: 1663
% 0.21/0.53  % (5048)Time elapsed: 0.118 s
% 0.21/0.53  % (5048)------------------------------
% 0.21/0.53  % (5048)------------------------------
% 0.21/0.53  % (5062)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (5065)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (5064)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (5063)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (5069)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (5069)Refutation not found, incomplete strategy% (5069)------------------------------
% 0.21/0.54  % (5069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5069)Memory used [KB]: 1663
% 0.21/0.54  % (5069)Time elapsed: 0.135 s
% 0.21/0.54  % (5069)------------------------------
% 0.21/0.54  % (5069)------------------------------
% 0.21/0.54  % (5052)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (5053)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (5073)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5070)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (5072)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (5052)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f43,f81,f142,f156,f173,f198])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    spl8_2 | ~spl8_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    $false | (spl8_2 | ~spl8_4)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f42,f137,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | ~spl8_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl8_4 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl8_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    spl8_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ~spl8_1 | ~spl8_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    $false | (~spl8_1 | ~spl8_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f141,f141,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,X3)) ) | ~spl8_1),
% 0.21/0.54    inference(forward_demodulation,[],[f96,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    spl8_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X2,k2_relat_1(k1_xboole_0))) ) | ~spl8_1),
% 0.21/0.54    inference(resolution,[],[f93,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK1(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),k1_xboole_0) | ~r2_hidden(X4,X5)) ) | ~spl8_1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r2_hidden(X4,X5) | ~r2_hidden(k4_tarski(X3,X4),k1_xboole_0) | ~r2_hidden(X4,X5)) ) | ~spl8_1),
% 0.21/0.54    inference(forward_demodulation,[],[f91,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),k1_xboole_0) | ~r2_hidden(X4,X5) | ~r2_hidden(X4,k5_xboole_0(X5,k1_xboole_0))) ) | ~spl8_1),
% 0.21/0.54    inference(resolution,[],[f85,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X1] : (r2_hidden(X1,k1_xboole_0) | ~r2_hidden(k4_tarski(X2,X1),k1_xboole_0)) ) | ~spl8_1),
% 0.21/0.54    inference(superposition,[],[f34,f37])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | ~spl8_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    spl8_5 <=> r2_hidden(sK3(k1_xboole_0),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ~spl8_1 | spl8_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    $false | (~spl8_1 | spl8_3)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f143,f143,f102])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | spl8_3),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f134,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK5(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ~v1_relat_1(k1_xboole_0) | spl8_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl8_3 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ~spl8_3 | spl8_4 | spl8_5 | ~spl8_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f84,f36,f139,f136,f132])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_1),
% 0.21/0.54    inference(superposition,[],[f22,f37])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl8_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    $false | spl8_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f44,f63,f33])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ~r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k1_xboole_0) | spl8_1),
% 0.21/0.54    inference(forward_demodulation,[],[f60,f25])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ~r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k5_xboole_0(k1_xboole_0,k1_xboole_0)) | spl8_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f45,f45,f30])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k1_xboole_0) | spl8_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f44,f33])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | spl8_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f38,f24])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl8_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f36])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~spl8_1 | ~spl8_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f17,f40,f36])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (5052)------------------------------
% 0.21/0.54  % (5052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5052)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (5052)Memory used [KB]: 6268
% 0.21/0.54  % (5052)Time elapsed: 0.129 s
% 0.21/0.54  % (5052)------------------------------
% 0.21/0.54  % (5052)------------------------------
% 0.21/0.54  % (5070)Refutation not found, incomplete strategy% (5070)------------------------------
% 0.21/0.54  % (5070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5070)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5070)Memory used [KB]: 10618
% 0.21/0.54  % (5070)Time elapsed: 0.130 s
% 0.21/0.54  % (5070)------------------------------
% 0.21/0.54  % (5070)------------------------------
% 0.21/0.54  % (5047)Success in time 0.177 s
%------------------------------------------------------------------------------
