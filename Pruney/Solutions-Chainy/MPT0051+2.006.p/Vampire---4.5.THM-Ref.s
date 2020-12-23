%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:55 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 139 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  155 ( 284 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f65,f95,f181,f186,f191,f258,f404,f451,f540])).

fof(f540,plain,
    ( ~ spl3_1
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl3_1
    | spl3_7 ),
    inference(subsumption_resolution,[],[f532,f463])).

fof(f463,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X0)),k2_xboole_0(X1,sK2))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f74,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f40,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f532,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f190,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f190,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f451,plain,
    ( ~ spl3_10
    | spl3_3 ),
    inference(avatar_split_clause,[],[f90,f62,f448])).

fof(f448,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f62,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f64,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f64,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f404,plain,
    ( spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f81,f38,f401])).

fof(f401,plain,
    ( spl3_9
  <=> r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f40,f40,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f258,plain,
    ( ~ spl3_8
    | ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f88,f62,f38,f255])).

fof(f255,plain,
    ( spl3_8
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f40,f64,f35])).

fof(f191,plain,
    ( ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f43,f188])).

fof(f43,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f45,f30])).

fof(f45,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f186,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f47,f38,f183])).

fof(f183,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f181,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f135,f92,f178])).

fof(f178,plain,
    ( spl3_5
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f135,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl3_4 ),
    inference(forward_demodulation,[],[f107,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f78,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f107,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(X0,X0))
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f94,f78,f35])).

fof(f94,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f66,f43,f92])).

fof(f66,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f45,f27,f35])).

fof(f65,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f54,f43,f62])).

fof(f54,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f45,f31])).

fof(f46,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f41,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:59:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (9048)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.48  % (9064)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.48  % (9056)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.49  % (9049)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (9053)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (9045)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (9065)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (9058)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (9062)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (9051)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (9061)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (9043)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (9046)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (9047)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (9066)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (9044)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (9057)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (9063)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (9052)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (9059)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (9055)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.52  % (9050)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (9054)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (9060)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 2.45/0.71  % (9058)Refutation found. Thanks to Tanya!
% 2.45/0.71  % SZS status Theorem for theBenchmark
% 2.45/0.71  % SZS output start Proof for theBenchmark
% 2.45/0.71  fof(f541,plain,(
% 2.45/0.71    $false),
% 2.45/0.71    inference(avatar_sat_refutation,[],[f41,f46,f65,f95,f181,f186,f191,f258,f404,f451,f540])).
% 2.45/0.71  fof(f540,plain,(
% 2.45/0.71    ~spl3_1 | spl3_7),
% 2.45/0.71    inference(avatar_contradiction_clause,[],[f539])).
% 2.45/0.71  fof(f539,plain,(
% 2.45/0.71    $false | (~spl3_1 | spl3_7)),
% 2.45/0.71    inference(subsumption_resolution,[],[f532,f463])).
% 2.45/0.71  fof(f463,plain,(
% 2.45/0.71    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X0)),k2_xboole_0(X1,sK2))) ) | ~spl3_1),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f52,f74,f35])).
% 2.45/0.71  fof(f35,plain,(
% 2.45/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.45/0.71    inference(cnf_transformation,[],[f21])).
% 2.45/0.71  fof(f21,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.45/0.71    inference(flattening,[],[f20])).
% 2.45/0.71  fof(f20,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.45/0.71    inference(ennf_transformation,[],[f3])).
% 2.45/0.71  fof(f3,axiom,(
% 2.45/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.45/0.71  fof(f74,plain,(
% 2.45/0.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f27,f32])).
% 2.45/0.71  fof(f32,plain,(
% 2.45/0.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 2.45/0.71    inference(cnf_transformation,[],[f17])).
% 2.45/0.71  fof(f17,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.45/0.71    inference(ennf_transformation,[],[f4])).
% 2.45/0.71  fof(f4,axiom,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 2.45/0.71  fof(f27,plain,(
% 2.45/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.45/0.71    inference(cnf_transformation,[],[f9])).
% 2.45/0.71  fof(f9,axiom,(
% 2.45/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.45/0.71  fof(f52,plain,(
% 2.45/0.71    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2))) ) | ~spl3_1),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f40,f31])).
% 2.45/0.71  fof(f31,plain,(
% 2.45/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.45/0.71    inference(cnf_transformation,[],[f16])).
% 2.45/0.71  fof(f16,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.45/0.71    inference(ennf_transformation,[],[f1])).
% 2.45/0.71  fof(f1,axiom,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.45/0.71  fof(f40,plain,(
% 2.45/0.71    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_1),
% 2.45/0.71    inference(avatar_component_clause,[],[f38])).
% 2.45/0.71  fof(f38,plain,(
% 2.45/0.71    spl3_1 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.45/0.71  fof(f532,plain,(
% 2.45/0.71    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | spl3_7),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f190,f75])).
% 2.45/0.71  fof(f75,plain,(
% 2.45/0.71    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.45/0.71    inference(resolution,[],[f32,f28])).
% 2.45/0.71  fof(f28,plain,(
% 2.45/0.71    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 2.45/0.71    inference(cnf_transformation,[],[f15])).
% 2.45/0.71  fof(f15,plain,(
% 2.45/0.71    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.45/0.71    inference(ennf_transformation,[],[f6])).
% 2.45/0.71  fof(f6,axiom,(
% 2.45/0.71    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 2.45/0.71  fof(f190,plain,(
% 2.45/0.71    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_7),
% 2.45/0.71    inference(avatar_component_clause,[],[f188])).
% 2.45/0.71  fof(f188,plain,(
% 2.45/0.71    spl3_7 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.45/0.71  fof(f451,plain,(
% 2.45/0.71    ~spl3_10 | spl3_3),
% 2.45/0.71    inference(avatar_split_clause,[],[f90,f62,f448])).
% 2.45/0.71  fof(f448,plain,(
% 2.45/0.71    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.45/0.71  fof(f62,plain,(
% 2.45/0.71    spl3_3 <=> r1_tarski(sK0,sK2)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.45/0.71  fof(f90,plain,(
% 2.45/0.71    k1_xboole_0 != k4_xboole_0(sK0,sK2) | spl3_3),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f64,f30])).
% 2.45/0.71  fof(f30,plain,(
% 2.45/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.45/0.71    inference(cnf_transformation,[],[f5])).
% 2.45/0.71  fof(f5,axiom,(
% 2.45/0.71    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 2.45/0.71  fof(f64,plain,(
% 2.45/0.71    ~r1_tarski(sK0,sK2) | spl3_3),
% 2.45/0.71    inference(avatar_component_clause,[],[f62])).
% 2.45/0.71  fof(f404,plain,(
% 2.45/0.71    spl3_9 | ~spl3_1),
% 2.45/0.71    inference(avatar_split_clause,[],[f81,f38,f401])).
% 2.45/0.71  fof(f401,plain,(
% 2.45/0.71    spl3_9 <=> r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.45/0.71  fof(f81,plain,(
% 2.45/0.71    r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2) | ~spl3_1),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f40,f40,f36])).
% 2.45/0.71  fof(f36,plain,(
% 2.45/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 2.45/0.71    inference(cnf_transformation,[],[f23])).
% 2.45/0.71  fof(f23,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.45/0.71    inference(flattening,[],[f22])).
% 2.45/0.71  fof(f22,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.45/0.71    inference(ennf_transformation,[],[f10])).
% 2.45/0.71  fof(f10,axiom,(
% 2.45/0.71    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.45/0.71  fof(f258,plain,(
% 2.45/0.71    ~spl3_8 | ~spl3_1 | spl3_3),
% 2.45/0.71    inference(avatar_split_clause,[],[f88,f62,f38,f255])).
% 2.45/0.71  fof(f255,plain,(
% 2.45/0.71    spl3_8 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.45/0.71  fof(f88,plain,(
% 2.45/0.71    ~r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | spl3_3)),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f40,f64,f35])).
% 2.45/0.71  fof(f191,plain,(
% 2.45/0.71    ~spl3_7 | spl3_2),
% 2.45/0.71    inference(avatar_split_clause,[],[f51,f43,f188])).
% 2.45/0.71  fof(f43,plain,(
% 2.45/0.71    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.45/0.71  fof(f51,plain,(
% 2.45/0.71    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f45,f30])).
% 2.45/0.71  fof(f45,plain,(
% 2.45/0.71    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 2.45/0.71    inference(avatar_component_clause,[],[f43])).
% 2.45/0.71  fof(f186,plain,(
% 2.45/0.71    spl3_6 | ~spl3_1),
% 2.45/0.71    inference(avatar_split_clause,[],[f47,f38,f183])).
% 2.45/0.71  fof(f183,plain,(
% 2.45/0.71    spl3_6 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.45/0.71  fof(f47,plain,(
% 2.45/0.71    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_1),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f40,f29])).
% 2.45/0.71  fof(f29,plain,(
% 2.45/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.45/0.71    inference(cnf_transformation,[],[f5])).
% 2.45/0.71  fof(f181,plain,(
% 2.45/0.71    ~spl3_5 | spl3_4),
% 2.45/0.71    inference(avatar_split_clause,[],[f135,f92,f178])).
% 2.45/0.71  fof(f178,plain,(
% 2.45/0.71    spl3_5 <=> r1_tarski(sK0,k1_xboole_0)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.45/0.71  fof(f92,plain,(
% 2.45/0.71    spl3_4 <=> r1_tarski(sK0,sK1)),
% 2.45/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.45/0.71  fof(f135,plain,(
% 2.45/0.71    ~r1_tarski(sK0,k1_xboole_0) | spl3_4),
% 2.45/0.71    inference(forward_demodulation,[],[f107,f117])).
% 2.45/0.71  fof(f117,plain,(
% 2.45/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f78,f26])).
% 2.45/0.71  fof(f26,plain,(
% 2.45/0.71    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.45/0.71    inference(cnf_transformation,[],[f14])).
% 2.45/0.71  fof(f14,plain,(
% 2.45/0.71    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.45/0.71    inference(ennf_transformation,[],[f7])).
% 2.45/0.71  fof(f7,axiom,(
% 2.45/0.71    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.45/0.71  fof(f78,plain,(
% 2.45/0.71    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f27,f33])).
% 2.45/0.71  fof(f33,plain,(
% 2.45/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.45/0.71    inference(cnf_transformation,[],[f18])).
% 2.45/0.71  fof(f18,plain,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.45/0.71    inference(ennf_transformation,[],[f8])).
% 2.45/0.71  fof(f8,axiom,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.45/0.71  fof(f107,plain,(
% 2.45/0.71    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(X0,X0))) ) | spl3_4),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f94,f78,f35])).
% 2.45/0.71  fof(f94,plain,(
% 2.45/0.71    ~r1_tarski(sK0,sK1) | spl3_4),
% 2.45/0.71    inference(avatar_component_clause,[],[f92])).
% 2.45/0.71  fof(f95,plain,(
% 2.45/0.71    ~spl3_4 | spl3_2),
% 2.45/0.71    inference(avatar_split_clause,[],[f66,f43,f92])).
% 2.45/0.71  fof(f66,plain,(
% 2.45/0.71    ~r1_tarski(sK0,sK1) | spl3_2),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f45,f27,f35])).
% 2.45/0.71  fof(f65,plain,(
% 2.45/0.71    ~spl3_3 | spl3_2),
% 2.45/0.71    inference(avatar_split_clause,[],[f54,f43,f62])).
% 2.45/0.71  fof(f54,plain,(
% 2.45/0.71    ~r1_tarski(sK0,sK2) | spl3_2),
% 2.45/0.71    inference(unit_resulting_resolution,[],[f45,f31])).
% 2.45/0.71  fof(f46,plain,(
% 2.45/0.71    ~spl3_2),
% 2.45/0.71    inference(avatar_split_clause,[],[f25,f43])).
% 2.45/0.71  fof(f25,plain,(
% 2.45/0.71    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.45/0.71    inference(cnf_transformation,[],[f13])).
% 2.45/0.71  fof(f13,plain,(
% 2.45/0.71    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.45/0.71    inference(ennf_transformation,[],[f12])).
% 2.45/0.71  fof(f12,negated_conjecture,(
% 2.45/0.71    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.45/0.71    inference(negated_conjecture,[],[f11])).
% 2.45/0.71  fof(f11,conjecture,(
% 2.45/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.45/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.45/0.71  fof(f41,plain,(
% 2.45/0.71    spl3_1),
% 2.45/0.71    inference(avatar_split_clause,[],[f24,f38])).
% 2.45/0.71  fof(f24,plain,(
% 2.45/0.71    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 2.45/0.71    inference(cnf_transformation,[],[f13])).
% 2.45/0.71  % SZS output end Proof for theBenchmark
% 2.45/0.71  % (9058)------------------------------
% 2.45/0.71  % (9058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.71  % (9058)Termination reason: Refutation
% 2.45/0.71  
% 2.45/0.71  % (9058)Memory used [KB]: 1918
% 2.45/0.71  % (9058)Time elapsed: 0.273 s
% 2.45/0.71  % (9058)------------------------------
% 2.45/0.71  % (9058)------------------------------
% 2.45/0.71  % (9042)Success in time 0.358 s
%------------------------------------------------------------------------------
