%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:11 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 116 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 162 expanded)
%              Number of equality atoms :   86 ( 151 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f308,f438])).

fof(f438,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f436,f169])).

fof(f169,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_tarski(X0,X1) ),
    inference(superposition,[],[f79,f62])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f436,plain,
    ( k1_xboole_0 = k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f425,f141])).

fof(f141,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f425,plain,
    ( k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))) = k4_xboole_0(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))))
    | spl5_1 ),
    inference(backward_demodulation,[],[f311,f421])).

fof(f421,plain,(
    ! [X6,X4,X5,X3] : k2_zfmisc_1(k2_tarski(X3,X6),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(k4_tarski(X3,X4),k4_tarski(X3,X5)),k2_tarski(k4_tarski(X6,X4),k4_tarski(X6,X5))) ),
    inference(forward_demodulation,[],[f410,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f115,f108])).

fof(f108,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f67,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f115,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f80,f107])).

fof(f107,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f63,f105])).

fof(f63,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f410,plain,(
    ! [X6,X4,X5,X3] : k2_zfmisc_1(k2_tarski(X3,X6),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(k4_tarski(X3,X4),k4_tarski(X3,X5)),k2_zfmisc_1(k2_tarski(X6,X6),k2_tarski(X4,X5))) ),
    inference(superposition,[],[f155,f151])).

fof(f155,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),X2),k2_zfmisc_1(k2_tarski(X1,X1),X2)) ),
    inference(forward_demodulation,[],[f154,f108])).

fof(f154,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_tarski(X1,X1),X2)) ),
    inference(forward_demodulation,[],[f117,f108])).

fof(f117,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),X2)) ),
    inference(definition_unfolding,[],[f82,f107,f107])).

fof(f82,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

% (25239)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f311,plain,
    ( k2_tarski(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))) = k4_xboole_0(k2_tarski(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f307,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f147,f108])).

fof(f147,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k4_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f112,f108])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k4_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f78,f107,f107,f107])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f307,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f308,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f109,f305])).

fof(f109,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(definition_unfolding,[],[f58,f105])).

fof(f58,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (25244)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (25238)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (25240)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (25251)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (25242)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (25256)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (25248)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (25248)Refutation not found, incomplete strategy% (25248)------------------------------
% 0.22/0.53  % (25248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25241)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (25248)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25248)Memory used [KB]: 10618
% 0.22/0.53  % (25248)Time elapsed: 0.090 s
% 0.22/0.53  % (25248)------------------------------
% 0.22/0.53  % (25248)------------------------------
% 0.22/0.53  % (25246)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (25252)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (25237)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (25253)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (25260)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.54  % (25259)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.54  % (25252)Refutation not found, incomplete strategy% (25252)------------------------------
% 1.36/0.54  % (25252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (25252)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (25252)Memory used [KB]: 10618
% 1.36/0.54  % (25252)Time elapsed: 0.133 s
% 1.36/0.54  % (25252)------------------------------
% 1.36/0.54  % (25252)------------------------------
% 1.36/0.54  % (25237)Refutation not found, incomplete strategy% (25237)------------------------------
% 1.36/0.54  % (25237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (25237)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (25237)Memory used [KB]: 1791
% 1.36/0.54  % (25237)Time elapsed: 0.126 s
% 1.36/0.54  % (25237)------------------------------
% 1.36/0.54  % (25237)------------------------------
% 1.36/0.54  % (25253)Refutation not found, incomplete strategy% (25253)------------------------------
% 1.36/0.54  % (25253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (25236)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.54  % (25246)Refutation not found, incomplete strategy% (25246)------------------------------
% 1.36/0.54  % (25246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (25243)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.36/0.54  % (25253)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (25253)Memory used [KB]: 1791
% 1.36/0.54  % (25253)Time elapsed: 0.115 s
% 1.36/0.54  % (25253)------------------------------
% 1.36/0.54  % (25253)------------------------------
% 1.36/0.54  % (25257)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.54  % (25263)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.54  % (25254)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.55  % (25263)Refutation not found, incomplete strategy% (25263)------------------------------
% 1.36/0.55  % (25263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25246)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25246)Memory used [KB]: 10746
% 1.36/0.55  % (25246)Time elapsed: 0.125 s
% 1.36/0.55  % (25246)------------------------------
% 1.36/0.55  % (25246)------------------------------
% 1.36/0.55  % (25256)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f441,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(avatar_sat_refutation,[],[f308,f438])).
% 1.36/0.55  fof(f438,plain,(
% 1.36/0.55    spl5_1),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f437])).
% 1.36/0.55  fof(f437,plain,(
% 1.36/0.55    $false | spl5_1),
% 1.36/0.55    inference(subsumption_resolution,[],[f436,f169])).
% 1.36/0.55  fof(f169,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X0,X1)) )),
% 1.36/0.55    inference(superposition,[],[f79,f62])).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.36/0.55  fof(f79,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f24])).
% 1.36/0.55  fof(f24,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.36/0.55  fof(f436,plain,(
% 1.36/0.55    k1_xboole_0 = k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))) | spl5_1),
% 1.36/0.55    inference(forward_demodulation,[],[f425,f141])).
% 1.36/0.55  fof(f141,plain,(
% 1.36/0.55    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 1.36/0.55    inference(equality_resolution,[],[f104])).
% 1.36/0.55  fof(f104,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f57])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.36/0.55    inference(flattening,[],[f56])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.36/0.55    inference(nnf_transformation,[],[f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f26])).
% 1.36/0.55  fof(f26,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.36/0.55  fof(f425,plain,(
% 1.36/0.55    k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))) = k4_xboole_0(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))) | spl5_1),
% 1.36/0.55    inference(backward_demodulation,[],[f311,f421])).
% 1.36/0.55  fof(f421,plain,(
% 1.36/0.55    ( ! [X6,X4,X5,X3] : (k2_zfmisc_1(k2_tarski(X3,X6),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(k4_tarski(X3,X4),k4_tarski(X3,X5)),k2_tarski(k4_tarski(X6,X4),k4_tarski(X6,X5)))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f410,f151])).
% 1.36/0.55  fof(f151,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f115,f108])).
% 1.36/0.55  fof(f108,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f67,f105])).
% 1.36/0.55  fof(f105,plain,(
% 1.36/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,axiom,(
% 1.36/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 1.36/0.55  fof(f67,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.36/0.55  fof(f115,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f80,f107])).
% 1.36/0.55  fof(f107,plain,(
% 1.36/0.55    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f63,f105])).
% 1.36/0.55  fof(f63,plain,(
% 1.36/0.55    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,axiom,(
% 1.36/0.55    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 1.36/0.55  fof(f80,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.36/0.55  fof(f410,plain,(
% 1.36/0.55    ( ! [X6,X4,X5,X3] : (k2_zfmisc_1(k2_tarski(X3,X6),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(k4_tarski(X3,X4),k4_tarski(X3,X5)),k2_zfmisc_1(k2_tarski(X6,X6),k2_tarski(X4,X5)))) )),
% 1.36/0.55    inference(superposition,[],[f155,f151])).
% 1.36/0.55  fof(f155,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),X2),k2_zfmisc_1(k2_tarski(X1,X1),X2))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f154,f108])).
% 1.36/0.55  fof(f154,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_tarski(X1,X1),X2))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f117,f108])).
% 1.36/0.55  fof(f117,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),X2))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f82,f107,f107])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 1.36/0.55  % (25239)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.55  fof(f311,plain,(
% 1.36/0.55    k2_tarski(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))) = k4_xboole_0(k2_tarski(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))) | spl5_1),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f307,f148])).
% 1.36/0.55  fof(f148,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 1.36/0.55    inference(forward_demodulation,[],[f147,f108])).
% 1.36/0.55  fof(f147,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k4_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X1)) | X0 = X1) )),
% 1.36/0.55    inference(forward_demodulation,[],[f112,f108])).
% 1.36/0.55  fof(f112,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k4_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) | X0 = X1) )),
% 1.36/0.55    inference(definition_unfolding,[],[f78,f107,f107,f107])).
% 1.36/0.55  fof(f78,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f49])).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.36/0.55    inference(nnf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,axiom,(
% 1.36/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.36/0.55  fof(f307,plain,(
% 1.36/0.55    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) | spl5_1),
% 1.36/0.55    inference(avatar_component_clause,[],[f305])).
% 1.36/0.55  fof(f305,plain,(
% 1.36/0.55    spl5_1 <=> k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.36/0.55  fof(f308,plain,(
% 1.36/0.55    ~spl5_1),
% 1.36/0.55    inference(avatar_split_clause,[],[f109,f305])).
% 1.36/0.55  fof(f109,plain,(
% 1.36/0.55    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),
% 1.36/0.55    inference(definition_unfolding,[],[f58,f105])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 1.36/0.55    inference(cnf_transformation,[],[f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f43])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.36/0.55    inference(ennf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.36/0.55    inference(negated_conjecture,[],[f27])).
% 1.36/0.55  fof(f27,conjecture,(
% 1.36/0.55    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (25256)------------------------------
% 1.36/0.55  % (25256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25256)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (25256)Memory used [KB]: 11129
% 1.36/0.55  % (25256)Time elapsed: 0.109 s
% 1.36/0.55  % (25256)------------------------------
% 1.36/0.55  % (25256)------------------------------
% 1.36/0.55  % (25228)Success in time 0.182 s
%------------------------------------------------------------------------------
