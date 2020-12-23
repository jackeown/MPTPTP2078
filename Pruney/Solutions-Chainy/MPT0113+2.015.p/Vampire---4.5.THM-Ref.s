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
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 275 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   26
%              Number of atoms          :  152 ( 500 expanded)
%              Number of equality atoms :   57 ( 204 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5049,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f1061,f5048])).

fof(f5048,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f5047])).

fof(f5047,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f1062,f5046])).

fof(f5046,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f5039,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f5039,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f36,f5005])).

fof(f5005,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f4674,f70])).

fof(f70,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4674,plain,(
    ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k4_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f1707,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1707,plain,(
    ! [X18] : k3_xboole_0(sK0,X18) = k4_xboole_0(k3_xboole_0(sK0,X18),sK2) ),
    inference(superposition,[],[f348,f1603])).

fof(f1603,plain,(
    ! [X11] : sK2 = k4_xboole_0(sK2,k3_xboole_0(sK0,X11)) ),
    inference(forward_demodulation,[],[f1595,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1595,plain,(
    ! [X11] : k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k3_xboole_0(sK0,X11)) ),
    inference(superposition,[],[f36,f1535])).

fof(f1535,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f1534,f242])).

fof(f242,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f239,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f239,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f238,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f238,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f226,f73])).

fof(f73,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(resolution,[],[f40,f69])).

fof(f69,plain,(
    ! [X6] : r1_tarski(X6,X6) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 != k3_xboole_0(X1,X1) ) ),
    inference(resolution,[],[f225,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(factoring,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1534,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f1509,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1509,plain,(
    ! [X0] : k3_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f1393,f83])).

fof(f83,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f44,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1393,plain,(
    ! [X1] : k3_xboole_0(sK2,X1) = k3_xboole_0(sK2,k4_xboole_0(X1,sK0)) ),
    inference(superposition,[],[f1239,f45])).

fof(f1239,plain,(
    ! [X22] : k3_xboole_0(sK2,X22) = k4_xboole_0(k3_xboole_0(sK2,X22),sK0) ),
    inference(superposition,[],[f348,f1186])).

fof(f1186,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f1137,f32])).

fof(f1137,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k3_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f453,f348])).

fof(f453,plain,(
    ! [X2,X3] : sK0 = k4_xboole_0(sK0,k3_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[],[f405,f45])).

fof(f405,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f390,f70])).

fof(f390,plain,(
    ! [X0] : k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f274,f348])).

fof(f274,plain,(
    ! [X11] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X11)) = k4_xboole_0(sK0,X11) ),
    inference(superposition,[],[f45,f70])).

fof(f348,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6 ),
    inference(forward_demodulation,[],[f341,f30])).

fof(f341,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f36,f275])).

fof(f275,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f45,f83])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1062,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1061,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1060])).

fof(f1060,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f470,f1059])).

fof(f1059,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl4_2 ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f470,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f360,f449])).

fof(f449,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f405,f348])).

fof(f360,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f275,f348])).

fof(f55,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f52,f48])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (11768)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (11766)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (11764)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (11776)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (11767)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (11780)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (11765)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (11771)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (11763)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (11774)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (11781)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (11770)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (11773)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (11772)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (11778)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (11777)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (11775)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (11779)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.67/0.58  % (11780)Refutation found. Thanks to Tanya!
% 1.67/0.58  % SZS status Theorem for theBenchmark
% 1.67/0.58  % SZS output start Proof for theBenchmark
% 1.67/0.58  fof(f5049,plain,(
% 1.67/0.58    $false),
% 1.67/0.58    inference(avatar_sat_refutation,[],[f55,f1061,f5048])).
% 1.67/0.58  fof(f5048,plain,(
% 1.67/0.58    spl4_1),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f5047])).
% 1.67/0.58  fof(f5047,plain,(
% 1.67/0.58    $false | spl4_1),
% 1.67/0.58    inference(subsumption_resolution,[],[f1062,f5046])).
% 1.67/0.58  fof(f5046,plain,(
% 1.67/0.58    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.67/0.58    inference(forward_demodulation,[],[f5039,f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f13])).
% 1.67/0.58  fof(f13,axiom,(
% 1.67/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.67/0.58  fof(f5039,plain,(
% 1.67/0.58    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)),
% 1.67/0.58    inference(superposition,[],[f36,f5005])).
% 1.67/0.58  fof(f5005,plain,(
% 1.67/0.58    sK0 = k3_xboole_0(sK0,sK1)),
% 1.67/0.58    inference(superposition,[],[f4674,f70])).
% 1.67/0.58  fof(f70,plain,(
% 1.67/0.58    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.67/0.58    inference(resolution,[],[f40,f27])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.67/0.58    inference(cnf_transformation,[],[f22])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.67/0.58    inference(ennf_transformation,[],[f16])).
% 1.67/0.58  fof(f16,negated_conjecture,(
% 1.67/0.58    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.67/0.58    inference(negated_conjecture,[],[f15])).
% 1.67/0.58  fof(f15,conjecture,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.67/0.58  fof(f40,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f20,plain,(
% 1.67/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.67/0.58    inference(ennf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,axiom,(
% 1.67/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.67/0.58  fof(f4674,plain,(
% 1.67/0.58    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k4_xboole_0(X1,sK2))) )),
% 1.67/0.58    inference(superposition,[],[f1707,f45])).
% 1.67/0.58  fof(f45,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f10])).
% 1.67/0.58  fof(f10,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.67/0.58  fof(f1707,plain,(
% 1.67/0.58    ( ! [X18] : (k3_xboole_0(sK0,X18) = k4_xboole_0(k3_xboole_0(sK0,X18),sK2)) )),
% 1.67/0.58    inference(superposition,[],[f348,f1603])).
% 1.67/0.58  fof(f1603,plain,(
% 1.67/0.58    ( ! [X11] : (sK2 = k4_xboole_0(sK2,k3_xboole_0(sK0,X11))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f1595,f30])).
% 1.67/0.58  fof(f30,plain,(
% 1.67/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f11])).
% 1.67/0.58  fof(f11,axiom,(
% 1.67/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.67/0.58  fof(f1595,plain,(
% 1.67/0.58    ( ! [X11] : (k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k3_xboole_0(sK0,X11))) )),
% 1.67/0.58    inference(superposition,[],[f36,f1535])).
% 1.67/0.58  fof(f1535,plain,(
% 1.67/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,X0))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f1534,f242])).
% 1.67/0.58  fof(f242,plain,(
% 1.67/0.58    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 1.67/0.58    inference(resolution,[],[f239,f41])).
% 1.67/0.58  fof(f41,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f25])).
% 1.67/0.58  fof(f25,plain,(
% 1.67/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(nnf_transformation,[],[f3])).
% 1.67/0.58  fof(f3,axiom,(
% 1.67/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.67/0.58  fof(f239,plain,(
% 1.67/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.67/0.58    inference(resolution,[],[f238,f37])).
% 1.67/0.58  fof(f37,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f24])).
% 1.67/0.58  fof(f24,plain,(
% 1.67/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).
% 1.67/0.58  fof(f23,plain,(
% 1.67/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f19,plain,(
% 1.67/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(ennf_transformation,[],[f17])).
% 1.67/0.58  fof(f17,plain,(
% 1.67/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(rectify,[],[f4])).
% 1.67/0.58  fof(f4,axiom,(
% 1.67/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.67/0.58  fof(f238,plain,(
% 1.67/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.67/0.58    inference(equality_resolution,[],[f229])).
% 1.67/0.58  fof(f229,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X0,X1)) )),
% 1.67/0.58    inference(forward_demodulation,[],[f226,f73])).
% 1.67/0.58  fof(f73,plain,(
% 1.67/0.58    ( ! [X4] : (k3_xboole_0(X4,X4) = X4) )),
% 1.67/0.58    inference(resolution,[],[f40,f69])).
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    ( ! [X6] : (r1_tarski(X6,X6)) )),
% 1.67/0.58    inference(superposition,[],[f31,f34])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f8])).
% 1.67/0.58  fof(f8,axiom,(
% 1.67/0.58    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f7])).
% 1.67/0.58  fof(f7,axiom,(
% 1.67/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.67/0.58  fof(f226,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 != k3_xboole_0(X1,X1)) )),
% 1.67/0.58    inference(resolution,[],[f225,f42])).
% 1.67/0.58  fof(f42,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f25])).
% 1.67/0.58  fof(f225,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 1.67/0.58    inference(factoring,[],[f39])).
% 1.67/0.58  fof(f39,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f24])).
% 1.67/0.58  fof(f1534,plain,(
% 1.67/0.58    ( ! [X0] : (k3_xboole_0(k1_xboole_0,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK0,X0))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f1509,f32])).
% 1.67/0.58  fof(f32,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f1])).
% 1.67/0.58  fof(f1,axiom,(
% 1.67/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.67/0.58  fof(f1509,plain,(
% 1.67/0.58    ( ! [X0] : (k3_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k3_xboole_0(sK0,X0))) )),
% 1.67/0.58    inference(superposition,[],[f1393,f83])).
% 1.67/0.58  fof(f83,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.67/0.58    inference(resolution,[],[f44,f31])).
% 1.67/0.58  fof(f44,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f26])).
% 1.67/0.58  fof(f26,plain,(
% 1.67/0.58    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.67/0.58    inference(nnf_transformation,[],[f5])).
% 1.67/0.58  fof(f5,axiom,(
% 1.67/0.58    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.67/0.58  fof(f1393,plain,(
% 1.67/0.58    ( ! [X1] : (k3_xboole_0(sK2,X1) = k3_xboole_0(sK2,k4_xboole_0(X1,sK0))) )),
% 1.67/0.58    inference(superposition,[],[f1239,f45])).
% 1.67/0.58  fof(f1239,plain,(
% 1.67/0.58    ( ! [X22] : (k3_xboole_0(sK2,X22) = k4_xboole_0(k3_xboole_0(sK2,X22),sK0)) )),
% 1.67/0.58    inference(superposition,[],[f348,f1186])).
% 1.67/0.58  fof(f1186,plain,(
% 1.67/0.58    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k3_xboole_0(sK2,X0))) )),
% 1.67/0.58    inference(superposition,[],[f1137,f32])).
% 1.67/0.58  fof(f1137,plain,(
% 1.67/0.58    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k3_xboole_0(X0,sK2))) )),
% 1.67/0.58    inference(superposition,[],[f453,f348])).
% 1.67/0.58  fof(f453,plain,(
% 1.67/0.58    ( ! [X2,X3] : (sK0 = k4_xboole_0(sK0,k3_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(sK1,sK2))))) )),
% 1.67/0.58    inference(superposition,[],[f405,f45])).
% 1.67/0.58  fof(f405,plain,(
% 1.67/0.58    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f390,f70])).
% 1.67/0.58  fof(f390,plain,(
% 1.67/0.58    ( ! [X0] : (k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) )),
% 1.67/0.58    inference(superposition,[],[f274,f348])).
% 1.67/0.58  fof(f274,plain,(
% 1.67/0.58    ( ! [X11] : (k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X11)) = k4_xboole_0(sK0,X11)) )),
% 1.67/0.58    inference(superposition,[],[f45,f70])).
% 1.67/0.58  fof(f348,plain,(
% 1.67/0.58    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6) )),
% 1.67/0.58    inference(forward_demodulation,[],[f341,f30])).
% 1.67/0.58  fof(f341,plain,(
% 1.67/0.58    ( ! [X6,X7] : (k5_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 1.67/0.58    inference(superposition,[],[f36,f275])).
% 1.67/0.58  fof(f275,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.67/0.58    inference(superposition,[],[f45,f83])).
% 1.67/0.58  fof(f36,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.58  fof(f1062,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl4_1),
% 1.67/0.58    inference(resolution,[],[f50,f43])).
% 1.67/0.58  fof(f43,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f26])).
% 1.67/0.58  fof(f50,plain,(
% 1.67/0.58    ~r1_tarski(sK0,sK1) | spl4_1),
% 1.67/0.58    inference(avatar_component_clause,[],[f48])).
% 1.67/0.58  fof(f48,plain,(
% 1.67/0.58    spl4_1 <=> r1_tarski(sK0,sK1)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.67/0.58  fof(f1061,plain,(
% 1.67/0.58    spl4_2),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f1060])).
% 1.67/0.58  fof(f1060,plain,(
% 1.67/0.58    $false | spl4_2),
% 1.67/0.58    inference(subsumption_resolution,[],[f470,f1059])).
% 1.67/0.58  fof(f1059,plain,(
% 1.67/0.58    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl4_2),
% 1.67/0.58    inference(resolution,[],[f54,f42])).
% 1.67/0.58  fof(f54,plain,(
% 1.67/0.58    ~r1_xboole_0(sK0,sK2) | spl4_2),
% 1.67/0.58    inference(avatar_component_clause,[],[f52])).
% 1.67/0.58  fof(f52,plain,(
% 1.67/0.58    spl4_2 <=> r1_xboole_0(sK0,sK2)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.67/0.58  fof(f470,plain,(
% 1.67/0.58    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.67/0.58    inference(superposition,[],[f360,f449])).
% 1.67/0.58  fof(f449,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,sK2)),
% 1.67/0.58    inference(superposition,[],[f405,f348])).
% 1.67/0.58  fof(f360,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 1.67/0.58    inference(superposition,[],[f275,f348])).
% 1.67/0.58  fof(f55,plain,(
% 1.67/0.58    ~spl4_1 | ~spl4_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f28,f52,f48])).
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.67/0.58    inference(cnf_transformation,[],[f22])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (11780)------------------------------
% 1.67/0.58  % (11780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (11780)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (11780)Memory used [KB]: 7931
% 1.67/0.58  % (11780)Time elapsed: 0.111 s
% 1.67/0.58  % (11780)------------------------------
% 1.67/0.58  % (11780)------------------------------
% 1.67/0.58  % (11760)Success in time 0.228 s
%------------------------------------------------------------------------------
