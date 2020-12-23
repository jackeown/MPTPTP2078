%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:35 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   61 (  86 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  134 ( 192 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f107,f119,f139,f154,f163])).

fof(f163,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f162])).

% (29194)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (29194)Refutation not found, incomplete strategy% (29194)------------------------------
% (29194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29194)Termination reason: Refutation not found, incomplete strategy

% (29194)Memory used [KB]: 1663
% (29194)Time elapsed: 0.112 s
% (29194)------------------------------
% (29194)------------------------------
% (29180)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (29186)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (29187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (29199)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f162,plain,
    ( $false
    | spl5_1
    | spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f161,f60])).

fof(f60,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f161,plain,
    ( sK0 = sK1
    | spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f159,f64])).

fof(f64,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f159,plain,
    ( sK0 = sK2
    | sK0 = sK1
    | ~ spl5_11 ),
    inference(resolution,[],[f138,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f138,plain,
    ( sP4(sK0,sK2,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_11
  <=> sP4(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f154,plain,
    ( spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f64,f150])).

fof(f150,plain,
    ( ! [X0] : sK0 = X0
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f145,f147])).

fof(f147,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | ~ spl5_6 ),
    inference(superposition,[],[f57,f140])).

fof(f140,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),X0)
    | ~ spl5_6 ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f103,plain,
    ( ! [X0] : r1_tarski(k1_tarski(sK0),X0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_6
  <=> ! [X0] : r1_tarski(k1_tarski(sK0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f57,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f145,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tarski(sK0)
        | sK0 = X0 )
    | ~ spl5_6 ),
    inference(superposition,[],[f140,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f139,plain,
    ( spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f125,f117,f137])).

fof(f117,plain,
    ( spl5_10
  <=> r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f125,plain,
    ( sP4(sK0,sK2,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f118,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f118,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl5_10
    | spl5_7 ),
    inference(avatar_split_clause,[],[f115,f105,f117])).

fof(f105,plain,
    ( spl5_7
  <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f115,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | spl5_7 ),
    inference(resolution,[],[f106,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f106,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl5_6
    | ~ spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f78,f67,f105,f102])).

fof(f67,plain,
    ( spl5_3
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
        | r1_tarski(k1_tarski(sK0),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f72,plain,
    ( ! [X0] : r1_tarski(k1_tarski(sK0),k2_xboole_0(X0,k2_tarski(sK1,sK2)))
    | ~ spl5_3 ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f68,plain,
    ( r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f65,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.36  ipcrm: permission denied for id (799145984)
% 0.19/0.36  ipcrm: permission denied for id (799211525)
% 0.19/0.37  ipcrm: permission denied for id (801964040)
% 0.19/0.37  ipcrm: permission denied for id (799277065)
% 0.19/0.37  ipcrm: permission denied for id (801996810)
% 0.19/0.37  ipcrm: permission denied for id (802029579)
% 0.19/0.37  ipcrm: permission denied for id (802127886)
% 0.19/0.38  ipcrm: permission denied for id (802193424)
% 0.19/0.38  ipcrm: permission denied for id (802226193)
% 0.19/0.38  ipcrm: permission denied for id (802258962)
% 0.19/0.38  ipcrm: permission denied for id (799539219)
% 0.19/0.38  ipcrm: permission denied for id (802291732)
% 0.19/0.38  ipcrm: permission denied for id (802324501)
% 0.19/0.38  ipcrm: permission denied for id (802357270)
% 0.19/0.39  ipcrm: permission denied for id (802390039)
% 0.19/0.39  ipcrm: permission denied for id (799604760)
% 0.19/0.39  ipcrm: permission denied for id (802422809)
% 0.19/0.39  ipcrm: permission denied for id (802455578)
% 0.19/0.39  ipcrm: permission denied for id (802488347)
% 0.19/0.39  ipcrm: permission denied for id (799735836)
% 0.19/0.39  ipcrm: permission denied for id (799768605)
% 0.19/0.40  ipcrm: permission denied for id (799834143)
% 0.19/0.40  ipcrm: permission denied for id (802684964)
% 0.19/0.40  ipcrm: permission denied for id (802717733)
% 0.19/0.40  ipcrm: permission denied for id (802750502)
% 0.19/0.41  ipcrm: permission denied for id (802783271)
% 0.19/0.41  ipcrm: permission denied for id (802816040)
% 0.19/0.41  ipcrm: permission denied for id (800063529)
% 0.19/0.41  ipcrm: permission denied for id (802848810)
% 0.19/0.41  ipcrm: permission denied for id (800129067)
% 0.19/0.41  ipcrm: permission denied for id (802881580)
% 0.19/0.42  ipcrm: permission denied for id (802979887)
% 0.19/0.42  ipcrm: permission denied for id (803012656)
% 0.19/0.42  ipcrm: permission denied for id (803045425)
% 0.19/0.42  ipcrm: permission denied for id (803143732)
% 0.19/0.42  ipcrm: permission denied for id (803176501)
% 0.19/0.43  ipcrm: permission denied for id (800194616)
% 0.19/0.43  ipcrm: permission denied for id (803307578)
% 0.19/0.44  ipcrm: permission denied for id (803504192)
% 0.19/0.44  ipcrm: permission denied for id (803602499)
% 0.19/0.44  ipcrm: permission denied for id (803635268)
% 0.19/0.44  ipcrm: permission denied for id (803668037)
% 0.19/0.45  ipcrm: permission denied for id (803766344)
% 0.19/0.45  ipcrm: permission denied for id (803799113)
% 0.19/0.45  ipcrm: permission denied for id (803831882)
% 0.19/0.45  ipcrm: permission denied for id (803864651)
% 0.19/0.45  ipcrm: permission denied for id (800587852)
% 0.19/0.45  ipcrm: permission denied for id (803897421)
% 0.19/0.46  ipcrm: permission denied for id (800653390)
% 0.19/0.46  ipcrm: permission denied for id (803930191)
% 0.19/0.46  ipcrm: permission denied for id (800718928)
% 0.19/0.46  ipcrm: permission denied for id (803962961)
% 0.19/0.46  ipcrm: permission denied for id (800784466)
% 0.19/0.46  ipcrm: permission denied for id (803995731)
% 0.19/0.46  ipcrm: permission denied for id (800850005)
% 0.19/0.47  ipcrm: permission denied for id (800882774)
% 0.19/0.47  ipcrm: permission denied for id (804061271)
% 0.19/0.47  ipcrm: permission denied for id (804126809)
% 0.19/0.47  ipcrm: permission denied for id (801013851)
% 0.19/0.47  ipcrm: permission denied for id (801046620)
% 0.19/0.47  ipcrm: permission denied for id (804192349)
% 0.19/0.48  ipcrm: permission denied for id (801079390)
% 0.19/0.48  ipcrm: permission denied for id (801112159)
% 0.19/0.48  ipcrm: permission denied for id (804225120)
% 0.19/0.48  ipcrm: permission denied for id (801144929)
% 0.19/0.48  ipcrm: permission denied for id (801177699)
% 0.19/0.48  ipcrm: permission denied for id (801210468)
% 0.19/0.48  ipcrm: permission denied for id (801243237)
% 0.19/0.49  ipcrm: permission denied for id (801276006)
% 0.19/0.49  ipcrm: permission denied for id (804290663)
% 0.19/0.49  ipcrm: permission denied for id (804323432)
% 0.19/0.49  ipcrm: permission denied for id (804388970)
% 0.19/0.49  ipcrm: permission denied for id (804421739)
% 0.19/0.49  ipcrm: permission denied for id (801341548)
% 0.19/0.50  ipcrm: permission denied for id (801374317)
% 0.19/0.50  ipcrm: permission denied for id (801407086)
% 0.19/0.50  ipcrm: permission denied for id (804454511)
% 0.19/0.50  ipcrm: permission denied for id (801439856)
% 0.19/0.50  ipcrm: permission denied for id (801472625)
% 0.19/0.50  ipcrm: permission denied for id (804520051)
% 0.19/0.51  ipcrm: permission denied for id (801505397)
% 0.19/0.51  ipcrm: permission denied for id (801538166)
% 0.19/0.51  ipcrm: permission denied for id (801570935)
% 0.19/0.51  ipcrm: permission denied for id (801603704)
% 0.19/0.51  ipcrm: permission denied for id (801636473)
% 0.19/0.51  ipcrm: permission denied for id (804585594)
% 0.19/0.51  ipcrm: permission denied for id (801702011)
% 0.19/0.52  ipcrm: permission denied for id (804651133)
% 0.19/0.52  ipcrm: permission denied for id (804716671)
% 0.75/0.63  % (29177)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.75/0.64  % (29184)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.75/0.64  % (29177)Refutation not found, incomplete strategy% (29177)------------------------------
% 0.75/0.64  % (29177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.75/0.64  % (29177)Termination reason: Refutation not found, incomplete strategy
% 0.75/0.64  
% 0.75/0.64  % (29177)Memory used [KB]: 1663
% 0.75/0.64  % (29177)Time elapsed: 0.066 s
% 0.75/0.64  % (29177)------------------------------
% 0.75/0.64  % (29177)------------------------------
% 1.15/0.65  % (29178)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.15/0.65  % (29185)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.15/0.66  % (29202)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.15/0.66  % (29202)Refutation found. Thanks to Tanya!
% 1.15/0.66  % SZS status Theorem for theBenchmark
% 1.15/0.66  % SZS output start Proof for theBenchmark
% 1.15/0.66  fof(f164,plain,(
% 1.15/0.66    $false),
% 1.15/0.66    inference(avatar_sat_refutation,[],[f61,f65,f69,f107,f119,f139,f154,f163])).
% 1.15/0.66  fof(f163,plain,(
% 1.15/0.66    spl5_1 | spl5_2 | ~spl5_11),
% 1.15/0.66    inference(avatar_contradiction_clause,[],[f162])).
% 1.15/0.67  % (29194)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.15/0.67  % (29194)Refutation not found, incomplete strategy% (29194)------------------------------
% 1.15/0.67  % (29194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.67  % (29194)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.67  
% 1.15/0.67  % (29194)Memory used [KB]: 1663
% 1.15/0.67  % (29194)Time elapsed: 0.112 s
% 1.15/0.67  % (29194)------------------------------
% 1.15/0.67  % (29194)------------------------------
% 1.15/0.68  % (29180)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.15/0.68  % (29186)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.15/0.68  % (29187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.15/0.69  % (29199)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.15/0.69  fof(f162,plain,(
% 1.15/0.69    $false | (spl5_1 | spl5_2 | ~spl5_11)),
% 1.15/0.69    inference(subsumption_resolution,[],[f161,f60])).
% 1.15/0.69  fof(f60,plain,(
% 1.15/0.69    sK0 != sK1 | spl5_1),
% 1.15/0.69    inference(avatar_component_clause,[],[f59])).
% 1.15/0.69  fof(f59,plain,(
% 1.15/0.69    spl5_1 <=> sK0 = sK1),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.15/0.69  fof(f161,plain,(
% 1.15/0.69    sK0 = sK1 | (spl5_2 | ~spl5_11)),
% 1.15/0.69    inference(subsumption_resolution,[],[f159,f64])).
% 1.15/0.69  fof(f64,plain,(
% 1.15/0.69    sK0 != sK2 | spl5_2),
% 1.15/0.69    inference(avatar_component_clause,[],[f63])).
% 1.15/0.69  fof(f63,plain,(
% 1.15/0.69    spl5_2 <=> sK0 = sK2),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.15/0.69  fof(f159,plain,(
% 1.15/0.69    sK0 = sK2 | sK0 = sK1 | ~spl5_11),
% 1.15/0.69    inference(resolution,[],[f138,f35])).
% 1.15/0.69  fof(f35,plain,(
% 1.15/0.69    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.15/0.69    inference(cnf_transformation,[],[f10])).
% 1.15/0.69  fof(f10,axiom,(
% 1.15/0.69    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.15/0.69  fof(f138,plain,(
% 1.15/0.69    sP4(sK0,sK2,sK1) | ~spl5_11),
% 1.15/0.69    inference(avatar_component_clause,[],[f137])).
% 1.15/0.69  fof(f137,plain,(
% 1.15/0.69    spl5_11 <=> sP4(sK0,sK2,sK1)),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.15/0.69  fof(f154,plain,(
% 1.15/0.69    spl5_2 | ~spl5_6),
% 1.15/0.69    inference(avatar_contradiction_clause,[],[f152])).
% 1.15/0.69  fof(f152,plain,(
% 1.15/0.69    $false | (spl5_2 | ~spl5_6)),
% 1.15/0.69    inference(subsumption_resolution,[],[f64,f150])).
% 1.15/0.69  fof(f150,plain,(
% 1.15/0.69    ( ! [X0] : (sK0 = X0) ) | ~spl5_6),
% 1.15/0.69    inference(subsumption_resolution,[],[f145,f147])).
% 1.15/0.69  fof(f147,plain,(
% 1.15/0.69    k1_xboole_0 != k1_tarski(sK0) | ~spl5_6),
% 1.15/0.69    inference(superposition,[],[f57,f140])).
% 1.15/0.69  fof(f140,plain,(
% 1.15/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),X0)) ) | ~spl5_6),
% 1.15/0.69    inference(resolution,[],[f103,f47])).
% 1.15/0.69  fof(f47,plain,(
% 1.15/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.15/0.69    inference(cnf_transformation,[],[f3])).
% 1.15/0.69  fof(f3,axiom,(
% 1.15/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.15/0.69  fof(f103,plain,(
% 1.15/0.69    ( ! [X0] : (r1_tarski(k1_tarski(sK0),X0)) ) | ~spl5_6),
% 1.15/0.69    inference(avatar_component_clause,[],[f102])).
% 1.15/0.69  fof(f102,plain,(
% 1.15/0.69    spl5_6 <=> ! [X0] : r1_tarski(k1_tarski(sK0),X0)),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.15/0.69  fof(f57,plain,(
% 1.15/0.69    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.15/0.69    inference(equality_resolution,[],[f43])).
% 1.15/0.69  fof(f43,plain,(
% 1.15/0.69    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.15/0.69    inference(cnf_transformation,[],[f15])).
% 1.15/0.69  fof(f15,axiom,(
% 1.15/0.69    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.15/0.69  fof(f145,plain,(
% 1.15/0.69    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK0) | sK0 = X0) ) | ~spl5_6),
% 1.15/0.69    inference(superposition,[],[f140,f42])).
% 1.15/0.69  fof(f42,plain,(
% 1.15/0.69    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.15/0.69    inference(cnf_transformation,[],[f15])).
% 1.15/0.69  fof(f139,plain,(
% 1.15/0.69    spl5_11 | ~spl5_10),
% 1.15/0.69    inference(avatar_split_clause,[],[f125,f117,f137])).
% 1.15/0.69  fof(f117,plain,(
% 1.15/0.69    spl5_10 <=> r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.15/0.69  fof(f125,plain,(
% 1.15/0.69    sP4(sK0,sK2,sK1) | ~spl5_10),
% 1.15/0.69    inference(resolution,[],[f118,f53])).
% 1.15/0.69  fof(f53,plain,(
% 1.15/0.69    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | sP4(X3,X1,X0)) )),
% 1.15/0.69    inference(equality_resolution,[],[f37])).
% 1.15/0.69  fof(f37,plain,(
% 1.15/0.69    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.15/0.69    inference(cnf_transformation,[],[f10])).
% 1.15/0.69  fof(f118,plain,(
% 1.15/0.69    r2_hidden(sK0,k2_tarski(sK1,sK2)) | ~spl5_10),
% 1.15/0.69    inference(avatar_component_clause,[],[f117])).
% 1.15/0.69  fof(f119,plain,(
% 1.15/0.69    spl5_10 | spl5_7),
% 1.15/0.69    inference(avatar_split_clause,[],[f115,f105,f117])).
% 1.15/0.69  fof(f105,plain,(
% 1.15/0.69    spl5_7 <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.15/0.69  fof(f115,plain,(
% 1.15/0.69    r2_hidden(sK0,k2_tarski(sK1,sK2)) | spl5_7),
% 1.15/0.69    inference(resolution,[],[f106,f44])).
% 1.15/0.69  fof(f44,plain,(
% 1.15/0.69    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f21])).
% 1.15/0.69  fof(f21,plain,(
% 1.15/0.69    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.15/0.69    inference(ennf_transformation,[],[f14])).
% 1.15/0.69  fof(f14,axiom,(
% 1.15/0.69    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.15/0.69  fof(f106,plain,(
% 1.15/0.69    ~r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) | spl5_7),
% 1.15/0.69    inference(avatar_component_clause,[],[f105])).
% 1.15/0.69  fof(f107,plain,(
% 1.15/0.69    spl5_6 | ~spl5_7 | ~spl5_3),
% 1.15/0.69    inference(avatar_split_clause,[],[f78,f67,f105,f102])).
% 1.15/0.69  fof(f67,plain,(
% 1.15/0.69    spl5_3 <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.15/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.15/0.69  fof(f78,plain,(
% 1.15/0.69    ( ! [X0] : (~r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) | r1_tarski(k1_tarski(sK0),X0)) ) | ~spl5_3),
% 1.15/0.69    inference(resolution,[],[f72,f49])).
% 1.15/0.69  fof(f49,plain,(
% 1.15/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 1.15/0.69    inference(cnf_transformation,[],[f23])).
% 1.15/0.69  fof(f23,plain,(
% 1.15/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.15/0.69    inference(flattening,[],[f22])).
% 1.15/0.69  fof(f22,plain,(
% 1.15/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.15/0.69    inference(ennf_transformation,[],[f8])).
% 1.15/0.69  fof(f8,axiom,(
% 1.15/0.69    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.15/0.69  fof(f72,plain,(
% 1.15/0.69    ( ! [X0] : (r1_tarski(k1_tarski(sK0),k2_xboole_0(X0,k2_tarski(sK1,sK2)))) ) | ~spl5_3),
% 1.15/0.69    inference(resolution,[],[f68,f30])).
% 1.15/0.69  fof(f30,plain,(
% 1.15/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.15/0.69    inference(cnf_transformation,[],[f19])).
% 1.15/0.69  fof(f19,plain,(
% 1.15/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.15/0.69    inference(ennf_transformation,[],[f5])).
% 1.15/0.69  fof(f5,axiom,(
% 1.15/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.15/0.69  fof(f68,plain,(
% 1.15/0.69    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl5_3),
% 1.15/0.69    inference(avatar_component_clause,[],[f67])).
% 1.15/0.69  fof(f69,plain,(
% 1.15/0.69    spl5_3),
% 1.15/0.69    inference(avatar_split_clause,[],[f24,f67])).
% 1.15/0.69  fof(f24,plain,(
% 1.15/0.69    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.15/0.69    inference(cnf_transformation,[],[f18])).
% 1.15/0.69  fof(f18,plain,(
% 1.15/0.69    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.15/0.69    inference(ennf_transformation,[],[f17])).
% 1.15/0.69  fof(f17,negated_conjecture,(
% 1.15/0.69    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.15/0.69    inference(negated_conjecture,[],[f16])).
% 1.15/0.69  fof(f16,conjecture,(
% 1.15/0.69    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.15/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.15/0.69  fof(f65,plain,(
% 1.15/0.69    ~spl5_2),
% 1.15/0.69    inference(avatar_split_clause,[],[f26,f63])).
% 1.15/0.69  fof(f26,plain,(
% 1.15/0.69    sK0 != sK2),
% 1.15/0.69    inference(cnf_transformation,[],[f18])).
% 1.15/0.69  fof(f61,plain,(
% 1.15/0.69    ~spl5_1),
% 1.15/0.69    inference(avatar_split_clause,[],[f25,f59])).
% 1.15/0.69  fof(f25,plain,(
% 1.15/0.69    sK0 != sK1),
% 1.15/0.69    inference(cnf_transformation,[],[f18])).
% 1.15/0.69  % SZS output end Proof for theBenchmark
% 1.15/0.69  % (29202)------------------------------
% 1.15/0.69  % (29202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.69  % (29202)Termination reason: Refutation
% 1.15/0.69  
% 1.15/0.69  % (29202)Memory used [KB]: 6268
% 1.15/0.69  % (29202)Time elapsed: 0.107 s
% 1.15/0.69  % (29202)------------------------------
% 1.15/0.69  % (29202)------------------------------
% 1.15/0.69  % (29002)Success in time 0.336 s
%------------------------------------------------------------------------------
