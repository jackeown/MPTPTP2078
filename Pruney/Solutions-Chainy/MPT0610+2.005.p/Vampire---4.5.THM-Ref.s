%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:31 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 107 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  161 ( 307 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f122,f126,f130,f150,f1074,f1086,f1089,f1121,f1140])).

fof(f1140,plain,
    ( spl11_1
    | ~ spl11_69 ),
    inference(avatar_split_clause,[],[f1129,f1114,f116])).

fof(f116,plain,
    ( spl11_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1114,plain,
    ( spl11_69
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_69])])).

fof(f1129,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl11_69 ),
    inference(trivial_inequality_removal,[],[f1127])).

fof(f1127,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl11_69 ),
    inference(superposition,[],[f107,f1115])).

fof(f1115,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl11_69 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1121,plain,
    ( ~ spl11_63
    | spl11_69
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f1111,f1084,f1114,f1081])).

fof(f1081,plain,
    ( spl11_63
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f1084,plain,
    ( spl11_64
  <=> k3_xboole_0(sK0,sK1) = k7_relat_1(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f1111,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl11_64 ),
    inference(superposition,[],[f74,f1085])).

fof(f1085,plain,
    ( k3_xboole_0(sK0,sK1) = k7_relat_1(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f1089,plain,
    ( ~ spl11_4
    | spl11_63 ),
    inference(avatar_split_clause,[],[f1087,f1081,f128])).

fof(f128,plain,
    ( spl11_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1087,plain,
    ( ~ v1_relat_1(sK0)
    | spl11_63 ),
    inference(resolution,[],[f1082,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1082,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl11_63 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1086,plain,
    ( ~ spl11_63
    | spl11_64
    | ~ spl11_61 ),
    inference(avatar_split_clause,[],[f1079,f1072,f1084,f1081])).

fof(f1072,plain,
    ( spl11_61
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f1079,plain,
    ( k3_xboole_0(sK0,sK1) = k7_relat_1(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl11_61 ),
    inference(resolution,[],[f1073,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f1073,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1074,plain,
    ( spl11_61
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f1070,f148,f128,f124,f1072])).

fof(f124,plain,
    ( spl11_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f148,plain,
    ( spl11_7
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1070,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f1063,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1063,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f953,f129])).

fof(f129,plain,
    ( v1_relat_1(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f953,plain,
    ( ! [X13] :
        ( ~ v1_relat_1(X13)
        | r1_tarski(k1_relat_1(k3_xboole_0(X13,sK1)),k3_xboole_0(k1_relat_1(X13),k1_relat_1(sK1))) )
    | ~ spl11_3 ),
    inference(resolution,[],[f80,f125])).

fof(f125,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f150,plain,
    ( spl11_7
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f146,f120,f148])).

fof(f120,plain,
    ( spl11_2
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f146,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl11_2 ),
    inference(resolution,[],[f106,f121])).

fof(f121,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f130,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f70,f128])).

fof(f70,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f126,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f71,f124])).

fof(f71,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f122,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f72,f120])).

fof(f72,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f73,f116])).

fof(f73,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (12729)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (12720)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (12720)Refutation not found, incomplete strategy% (12720)------------------------------
% 0.22/0.49  % (12720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12720)Memory used [KB]: 10618
% 0.22/0.49  % (12720)Time elapsed: 0.074 s
% 0.22/0.49  % (12720)------------------------------
% 0.22/0.49  % (12720)------------------------------
% 0.22/0.50  % (12721)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (12722)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (12732)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (12719)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12728)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (12734)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (12730)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (12725)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (12731)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (12724)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (12727)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.54  % (12723)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.54  % (12726)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.54  % (12738)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  % (12733)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.55  % (12737)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.55  % (12735)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.56  % (12739)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.56  % (12739)Refutation not found, incomplete strategy% (12739)------------------------------
% 0.22/0.56  % (12739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12739)Memory used [KB]: 10618
% 0.22/0.56  % (12739)Time elapsed: 0.125 s
% 0.22/0.56  % (12739)------------------------------
% 0.22/0.56  % (12739)------------------------------
% 0.22/0.57  % (12736)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.84/0.61  % (12725)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.61  % SZS output start Proof for theBenchmark
% 1.84/0.61  fof(f1141,plain,(
% 1.84/0.61    $false),
% 1.84/0.61    inference(avatar_sat_refutation,[],[f118,f122,f126,f130,f150,f1074,f1086,f1089,f1121,f1140])).
% 1.84/0.61  fof(f1140,plain,(
% 1.84/0.61    spl11_1 | ~spl11_69),
% 1.84/0.61    inference(avatar_split_clause,[],[f1129,f1114,f116])).
% 1.84/0.61  fof(f116,plain,(
% 1.84/0.61    spl11_1 <=> r1_xboole_0(sK0,sK1)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.84/0.61  fof(f1114,plain,(
% 1.84/0.61    spl11_69 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_69])])).
% 1.84/0.61  fof(f1129,plain,(
% 1.84/0.61    r1_xboole_0(sK0,sK1) | ~spl11_69),
% 1.84/0.61    inference(trivial_inequality_removal,[],[f1127])).
% 1.84/0.61  fof(f1127,plain,(
% 1.84/0.61    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl11_69),
% 1.84/0.61    inference(superposition,[],[f107,f1115])).
% 1.84/0.61  fof(f1115,plain,(
% 1.84/0.61    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl11_69),
% 1.84/0.61    inference(avatar_component_clause,[],[f1114])).
% 1.84/0.61  fof(f107,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f69])).
% 1.84/0.61  fof(f69,plain,(
% 1.84/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.84/0.61    inference(nnf_transformation,[],[f1])).
% 1.84/0.61  fof(f1,axiom,(
% 1.84/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.84/0.61  fof(f1121,plain,(
% 1.84/0.61    ~spl11_63 | spl11_69 | ~spl11_64),
% 1.84/0.61    inference(avatar_split_clause,[],[f1111,f1084,f1114,f1081])).
% 1.84/0.61  fof(f1081,plain,(
% 1.84/0.61    spl11_63 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).
% 1.84/0.61  fof(f1084,plain,(
% 1.84/0.61    spl11_64 <=> k3_xboole_0(sK0,sK1) = k7_relat_1(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).
% 1.84/0.61  fof(f1111,plain,(
% 1.84/0.61    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~spl11_64),
% 1.84/0.61    inference(superposition,[],[f74,f1085])).
% 1.84/0.61  fof(f1085,plain,(
% 1.84/0.61    k3_xboole_0(sK0,sK1) = k7_relat_1(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl11_64),
% 1.84/0.61    inference(avatar_component_clause,[],[f1084])).
% 1.84/0.61  fof(f74,plain,(
% 1.84/0.61    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f26])).
% 1.84/0.61  fof(f26,plain,(
% 1.84/0.61    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f9])).
% 1.84/0.61  fof(f9,axiom,(
% 1.84/0.61    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 1.84/0.61  fof(f1089,plain,(
% 1.84/0.61    ~spl11_4 | spl11_63),
% 1.84/0.61    inference(avatar_split_clause,[],[f1087,f1081,f128])).
% 1.84/0.61  fof(f128,plain,(
% 1.84/0.61    spl11_4 <=> v1_relat_1(sK0)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.84/0.61  fof(f1087,plain,(
% 1.84/0.61    ~v1_relat_1(sK0) | spl11_63),
% 1.84/0.61    inference(resolution,[],[f1082,f93])).
% 1.84/0.61  fof(f93,plain,(
% 1.84/0.61    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f36])).
% 1.84/0.61  fof(f36,plain,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f8])).
% 1.84/0.61  fof(f8,axiom,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.84/0.61  fof(f1082,plain,(
% 1.84/0.61    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl11_63),
% 1.84/0.61    inference(avatar_component_clause,[],[f1081])).
% 1.84/0.61  fof(f1086,plain,(
% 1.84/0.61    ~spl11_63 | spl11_64 | ~spl11_61),
% 1.84/0.61    inference(avatar_split_clause,[],[f1079,f1072,f1084,f1081])).
% 1.84/0.61  fof(f1072,plain,(
% 1.84/0.61    spl11_61 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).
% 1.84/0.61  fof(f1079,plain,(
% 1.84/0.61    k3_xboole_0(sK0,sK1) = k7_relat_1(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~spl11_61),
% 1.84/0.61    inference(resolution,[],[f1073,f97])).
% 1.84/0.61  fof(f97,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f41])).
% 1.84/0.61  fof(f41,plain,(
% 1.84/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.84/0.61    inference(flattening,[],[f40])).
% 1.84/0.61  fof(f40,plain,(
% 1.84/0.61    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f19])).
% 1.84/0.61  fof(f19,axiom,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.84/0.61  fof(f1073,plain,(
% 1.84/0.61    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl11_61),
% 1.84/0.61    inference(avatar_component_clause,[],[f1072])).
% 1.84/0.61  fof(f1074,plain,(
% 1.84/0.61    spl11_61 | ~spl11_3 | ~spl11_4 | ~spl11_7),
% 1.84/0.61    inference(avatar_split_clause,[],[f1070,f148,f128,f124,f1072])).
% 1.84/0.61  fof(f124,plain,(
% 1.84/0.61    spl11_3 <=> v1_relat_1(sK1)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.84/0.61  fof(f148,plain,(
% 1.84/0.61    spl11_7 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.84/0.61  fof(f1070,plain,(
% 1.84/0.61    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl11_3 | ~spl11_4 | ~spl11_7)),
% 1.84/0.61    inference(forward_demodulation,[],[f1063,f149])).
% 1.84/0.61  fof(f149,plain,(
% 1.84/0.61    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl11_7),
% 1.84/0.61    inference(avatar_component_clause,[],[f148])).
% 1.84/0.61  fof(f1063,plain,(
% 1.84/0.61    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) | (~spl11_3 | ~spl11_4)),
% 1.84/0.61    inference(resolution,[],[f953,f129])).
% 1.84/0.61  fof(f129,plain,(
% 1.84/0.61    v1_relat_1(sK0) | ~spl11_4),
% 1.84/0.61    inference(avatar_component_clause,[],[f128])).
% 1.84/0.61  fof(f953,plain,(
% 1.84/0.61    ( ! [X13] : (~v1_relat_1(X13) | r1_tarski(k1_relat_1(k3_xboole_0(X13,sK1)),k3_xboole_0(k1_relat_1(X13),k1_relat_1(sK1)))) ) | ~spl11_3),
% 1.84/0.61    inference(resolution,[],[f80,f125])).
% 1.84/0.61  fof(f125,plain,(
% 1.84/0.61    v1_relat_1(sK1) | ~spl11_3),
% 1.84/0.61    inference(avatar_component_clause,[],[f124])).
% 1.84/0.61  fof(f80,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f31])).
% 1.84/0.61  fof(f31,plain,(
% 1.84/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f13])).
% 1.84/0.61  fof(f13,axiom,(
% 1.84/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 1.84/0.61  fof(f150,plain,(
% 1.84/0.61    spl11_7 | ~spl11_2),
% 1.84/0.61    inference(avatar_split_clause,[],[f146,f120,f148])).
% 1.84/0.61  fof(f120,plain,(
% 1.84/0.61    spl11_2 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.84/0.61  fof(f146,plain,(
% 1.84/0.61    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl11_2),
% 1.84/0.61    inference(resolution,[],[f106,f121])).
% 1.84/0.61  fof(f121,plain,(
% 1.84/0.61    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl11_2),
% 1.84/0.61    inference(avatar_component_clause,[],[f120])).
% 1.84/0.61  fof(f106,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f69])).
% 1.84/0.61  fof(f130,plain,(
% 1.84/0.61    spl11_4),
% 1.84/0.61    inference(avatar_split_clause,[],[f70,f128])).
% 1.84/0.61  fof(f70,plain,(
% 1.84/0.61    v1_relat_1(sK0)),
% 1.84/0.61    inference(cnf_transformation,[],[f50])).
% 1.84/0.61  fof(f50,plain,(
% 1.84/0.61    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.84/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f49,f48])).
% 1.84/0.61  fof(f48,plain,(
% 1.84/0.61    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.84/0.61    introduced(choice_axiom,[])).
% 1.84/0.61  fof(f49,plain,(
% 1.84/0.61    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.84/0.61    introduced(choice_axiom,[])).
% 1.84/0.61  fof(f25,plain,(
% 1.84/0.61    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.84/0.61    inference(flattening,[],[f24])).
% 1.84/0.61  fof(f24,plain,(
% 1.84/0.61    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f22])).
% 1.84/0.61  fof(f22,negated_conjecture,(
% 1.84/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.84/0.61    inference(negated_conjecture,[],[f21])).
% 1.84/0.61  fof(f21,conjecture,(
% 1.84/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 1.84/0.61  fof(f126,plain,(
% 1.84/0.61    spl11_3),
% 1.84/0.61    inference(avatar_split_clause,[],[f71,f124])).
% 1.84/0.61  fof(f71,plain,(
% 1.84/0.61    v1_relat_1(sK1)),
% 1.84/0.61    inference(cnf_transformation,[],[f50])).
% 1.84/0.61  fof(f122,plain,(
% 1.84/0.61    spl11_2),
% 1.84/0.61    inference(avatar_split_clause,[],[f72,f120])).
% 1.84/0.61  fof(f72,plain,(
% 1.84/0.61    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.84/0.61    inference(cnf_transformation,[],[f50])).
% 1.84/0.61  fof(f118,plain,(
% 1.84/0.61    ~spl11_1),
% 1.84/0.61    inference(avatar_split_clause,[],[f73,f116])).
% 1.84/0.61  fof(f73,plain,(
% 1.84/0.61    ~r1_xboole_0(sK0,sK1)),
% 1.84/0.61    inference(cnf_transformation,[],[f50])).
% 1.84/0.61  % SZS output end Proof for theBenchmark
% 1.84/0.61  % (12725)------------------------------
% 1.84/0.61  % (12725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (12725)Termination reason: Refutation
% 1.84/0.61  
% 1.84/0.61  % (12725)Memory used [KB]: 11385
% 1.84/0.61  % (12725)Time elapsed: 0.184 s
% 1.84/0.61  % (12725)------------------------------
% 1.84/0.61  % (12725)------------------------------
% 1.84/0.61  % (12718)Success in time 0.242 s
%------------------------------------------------------------------------------
