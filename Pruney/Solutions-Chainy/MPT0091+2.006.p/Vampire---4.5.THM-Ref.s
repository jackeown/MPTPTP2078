%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 180 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f45,f49,f72,f106,f131])).

fof(f131,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f124,f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f105,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f105,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_14
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f106,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f101,f69,f47,f20,f103])).

fof(f20,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,
    ( spl3_10
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f101,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f96,f71])).

fof(f71,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f96,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f48,f22])).

fof(f22,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f48,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f72,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f43,f25,f69])).

% (16956)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
fof(f25,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f49,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f33,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
          & r1_xboole_0(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (16957)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (16955)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (16948)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (16954)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (16949)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (16953)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (16953)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f45,f49,f72,f106,f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    spl3_3 | ~spl3_4 | ~spl3_14),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    $false | (spl3_3 | ~spl3_4 | ~spl3_14)),
% 0.21/0.45    inference(subsumption_resolution,[],[f124,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_14)),
% 0.21/0.45    inference(resolution,[],[f105,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl3_4 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    r1_xboole_0(sK1,sK0) | ~spl3_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    spl3_14 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl3_14 | ~spl3_1 | ~spl3_7 | ~spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f69,f47,f20,f103])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl3_10 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    r1_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_7 | ~spl3_10)),
% 0.21/0.45    inference(forward_demodulation,[],[f96,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_1 | ~spl3_7)),
% 0.21/0.45    inference(resolution,[],[f48,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f20])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f47])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl3_10 | ~spl3_2 | ~spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f64,f43,f25,f69])).
% 0.21/0.45  % (16956)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_6)),
% 0.21/0.45    inference(resolution,[],[f44,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f25])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f43])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f18,f47])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f43])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f35])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f12,f30])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f4])).
% 0.21/0.45  fof(f4,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f14,f20])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (16953)------------------------------
% 0.21/0.45  % (16953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16953)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (16953)Memory used [KB]: 10618
% 0.21/0.45  % (16953)Time elapsed: 0.006 s
% 0.21/0.45  % (16953)------------------------------
% 0.21/0.45  % (16953)------------------------------
% 0.21/0.45  % (16947)Success in time 0.09 s
%------------------------------------------------------------------------------
