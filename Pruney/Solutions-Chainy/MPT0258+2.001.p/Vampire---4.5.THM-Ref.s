%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   65 (  95 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 193 expanded)
%              Number of equality atoms :   51 (  78 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f832,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f128,f500,f626,f825])).

fof(f825,plain,
    ( ~ spl3_11
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f823,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f823,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | ~ spl3_11
    | spl3_15 ),
    inference(forward_demodulation,[],[f822,f526])).

fof(f526,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tarski(sK0,sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f499,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f499,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl3_11
  <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f822,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k4_xboole_0(k2_tarski(sK0,sK2),k2_xboole_0(sK1,k2_tarski(sK0,sK2))))
    | spl3_15 ),
    inference(forward_demodulation,[],[f814,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f814,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k4_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k2_tarski(sK0,sK2)))
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f625,f259])).

fof(f259,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k5_xboole_0(X3,k4_xboole_0(X3,X2))
      | r1_xboole_0(X2,X3) ) ),
    inference(backward_demodulation,[],[f184,f226])).

fof(f226,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f77,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f184,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X2))
      | r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f85,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f52,f57,f57])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f57])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f625,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl3_15
  <=> r1_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f626,plain,
    ( ~ spl3_15
    | spl3_5 ),
    inference(avatar_split_clause,[],[f129,f125,f623])).

fof(f125,plain,
    ( spl3_5
  <=> k2_tarski(sK0,sK2) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f129,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f127,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f127,plain,
    ( k2_tarski(sK0,sK2) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f500,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f348,f95,f90,f497])).

fof(f90,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f95,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f348,plain,
    ( sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f92,f97,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f97,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f92,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f128,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f78,f125])).

fof(f78,plain,(
    k2_tarski(sK0,sK2) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f45,plain,(
    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f98,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f95])).

fof(f44,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:42:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (9038)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (9040)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (9042)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (9047)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (9052)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (9050)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (9037)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (9043)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (9044)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (9051)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (9039)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (9045)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (9048)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (9049)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (9046)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (9041)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (9052)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f832,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f93,f98,f128,f500,f626,f825])).
% 1.40/0.54  fof(f825,plain,(
% 1.40/0.54    ~spl3_11 | spl3_15),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f824])).
% 1.40/0.54  fof(f824,plain,(
% 1.40/0.54    $false | (~spl3_11 | spl3_15)),
% 1.40/0.54    inference(subsumption_resolution,[],[f823,f46])).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f22])).
% 1.40/0.54  fof(f22,axiom,(
% 1.40/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.40/0.54  fof(f823,plain,(
% 1.40/0.54    k1_xboole_0 != k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | (~spl3_11 | spl3_15)),
% 1.40/0.54    inference(forward_demodulation,[],[f822,f526])).
% 1.40/0.54  fof(f526,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(sK1,k2_tarski(sK0,sK2)) | ~spl3_11),
% 1.40/0.54    inference(superposition,[],[f499,f51])).
% 1.40/0.54  fof(f51,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.40/0.54  fof(f499,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | ~spl3_11),
% 1.40/0.54    inference(avatar_component_clause,[],[f497])).
% 1.40/0.54  fof(f497,plain,(
% 1.40/0.54    spl3_11 <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.40/0.54  fof(f822,plain,(
% 1.40/0.54    k1_xboole_0 != k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k4_xboole_0(k2_tarski(sK0,sK2),k2_xboole_0(sK1,k2_tarski(sK0,sK2)))) | spl3_15),
% 1.40/0.54    inference(forward_demodulation,[],[f814,f72])).
% 1.40/0.54  fof(f72,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.40/0.54  fof(f814,plain,(
% 1.40/0.54    k1_xboole_0 != k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k4_xboole_0(k4_xboole_0(k2_tarski(sK0,sK2),sK1),k2_tarski(sK0,sK2))) | spl3_15),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f625,f259])).
% 1.40/0.54  fof(f259,plain,(
% 1.40/0.54    ( ! [X2,X3] : (k1_xboole_0 != k5_xboole_0(X3,k4_xboole_0(X3,X2)) | r1_xboole_0(X2,X3)) )),
% 1.40/0.54    inference(backward_demodulation,[],[f184,f226])).
% 1.40/0.54  fof(f226,plain,(
% 1.40/0.54    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 1.40/0.54    inference(superposition,[],[f77,f81])).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f56,f57])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f16,axiom,(
% 1.40/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,axiom,(
% 1.40/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f55,f57])).
% 1.40/0.54  fof(f55,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.40/0.54  fof(f184,plain,(
% 1.40/0.54    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X2)) | r1_xboole_0(X2,X3)) )),
% 1.40/0.54    inference(superposition,[],[f85,f79])).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f52,f57,f57])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.40/0.54  fof(f85,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f67,f57])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.40/0.54    inference(nnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.40/0.54  fof(f625,plain,(
% 1.40/0.54    ~r1_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl3_15),
% 1.40/0.54    inference(avatar_component_clause,[],[f623])).
% 1.40/0.54  fof(f623,plain,(
% 1.40/0.54    spl3_15 <=> r1_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.40/0.54  fof(f626,plain,(
% 1.40/0.54    ~spl3_15 | spl3_5),
% 1.40/0.54    inference(avatar_split_clause,[],[f129,f125,f623])).
% 1.40/0.54  fof(f125,plain,(
% 1.40/0.54    spl3_5 <=> k2_tarski(sK0,sK2) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.40/0.54  fof(f129,plain,(
% 1.40/0.54    ~r1_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl3_5),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f127,f64])).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f39])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.40/0.54    inference(nnf_transformation,[],[f20])).
% 1.40/0.54  fof(f20,axiom,(
% 1.40/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.40/0.54  fof(f127,plain,(
% 1.40/0.54    k2_tarski(sK0,sK2) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl3_5),
% 1.40/0.54    inference(avatar_component_clause,[],[f125])).
% 1.40/0.55  fof(f500,plain,(
% 1.40/0.55    spl3_11 | ~spl3_1 | ~spl3_2),
% 1.40/0.55    inference(avatar_split_clause,[],[f348,f95,f90,f497])).
% 1.40/0.55  fof(f90,plain,(
% 1.40/0.55    spl3_1 <=> r2_hidden(sK0,sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.40/0.55  fof(f95,plain,(
% 1.40/0.55    spl3_2 <=> r2_hidden(sK2,sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.40/0.55  fof(f348,plain,(
% 1.40/0.55    sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) | (~spl3_1 | ~spl3_2)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f92,f97,f75])).
% 1.40/0.55  fof(f75,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.40/0.55    inference(flattening,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.40/0.55  fof(f97,plain,(
% 1.40/0.55    r2_hidden(sK2,sK1) | ~spl3_2),
% 1.40/0.55    inference(avatar_component_clause,[],[f95])).
% 1.40/0.55  fof(f92,plain,(
% 1.40/0.55    r2_hidden(sK0,sK1) | ~spl3_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f90])).
% 1.40/0.55  fof(f128,plain,(
% 1.40/0.55    ~spl3_5),
% 1.40/0.55    inference(avatar_split_clause,[],[f78,f125])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    k2_tarski(sK0,sK2) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.40/0.55    inference(definition_unfolding,[],[f45,f57])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.40/0.55    inference(flattening,[],[f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f28])).
% 1.40/0.55  fof(f28,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.40/0.55    inference(negated_conjecture,[],[f27])).
% 1.40/0.55  fof(f27,conjecture,(
% 1.40/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.40/0.55  fof(f98,plain,(
% 1.40/0.55    spl3_2),
% 1.40/0.55    inference(avatar_split_clause,[],[f44,f95])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    r2_hidden(sK2,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  fof(f93,plain,(
% 1.40/0.55    spl3_1),
% 1.40/0.55    inference(avatar_split_clause,[],[f43,f90])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    r2_hidden(sK0,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f38])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (9052)------------------------------
% 1.40/0.55  % (9052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (9052)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (9052)Memory used [KB]: 11257
% 1.40/0.55  % (9052)Time elapsed: 0.059 s
% 1.40/0.55  % (9052)------------------------------
% 1.40/0.55  % (9052)------------------------------
% 1.40/0.55  % (9036)Success in time 0.186 s
%------------------------------------------------------------------------------
