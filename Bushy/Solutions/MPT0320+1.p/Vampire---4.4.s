%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t132_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   52 (  95 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 136 expanded)
%              Number of equality atoms :   45 (  95 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f54,f621,f626,f629,f634,f637])).

fof(f637,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f635])).

fof(f635,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f631,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',t41_enumset1)).

fof(f631,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl3_7 ),
    inference(superposition,[],[f620,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',t120_zfmisc_1)).

fof(f620,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl3_7
  <=> k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f634,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f632,f227])).

fof(f227,plain,(
    ! [X30,X31,X29] : k2_zfmisc_1(X31,k2_tarski(X29,X30)) = k2_zfmisc_1(X31,k2_tarski(X30,X29)) ),
    inference(forward_demodulation,[],[f183,f36])).

fof(f183,plain,(
    ! [X30,X31,X29] : k2_zfmisc_1(X31,k2_tarski(X29,X30)) = k2_zfmisc_1(X31,k2_xboole_0(k1_tarski(X30),k1_tarski(X29))) ),
    inference(superposition,[],[f161,f36])).

fof(f161,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_zfmisc_1(X7,k2_xboole_0(X9,X8)) ),
    inference(superposition,[],[f87,f39])).

fof(f87,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_zfmisc_1(X7,X9),k2_zfmisc_1(X7,X8)) ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f632,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_tarski(sK1,sK0))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f630,f36])).

fof(f630,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f620,f87])).

fof(f629,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f627])).

fof(f627,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f623,f36])).

fof(f623,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f614,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f614,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl3_5
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f626,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f624,f135])).

fof(f135,plain,(
    ! [X26,X27,X25] : k2_zfmisc_1(k2_tarski(X25,X26),X27) = k2_zfmisc_1(k2_tarski(X26,X25),X27) ),
    inference(forward_demodulation,[],[f112,f36])).

fof(f112,plain,(
    ! [X26,X27,X25] : k2_zfmisc_1(k2_tarski(X25,X26),X27) = k2_zfmisc_1(k2_xboole_0(k1_tarski(X26),k1_tarski(X25)),X27) ),
    inference(superposition,[],[f95,f36])).

fof(f95,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(k2_xboole_0(X3,X5),X4) = k2_zfmisc_1(k2_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f80,f38])).

fof(f80,plain,(
    ! [X6,X7,X5] : k2_zfmisc_1(k2_xboole_0(X5,X7),X6) = k2_xboole_0(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X5,X6)) ),
    inference(superposition,[],[f38,f35])).

fof(f624,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k2_tarski(sK1,sK0),sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f622,f36])).

fof(f622,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f614,f80])).

fof(f621,plain,
    ( ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f28,f619,f613])).

fof(f28,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',t132_zfmisc_1)).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f52,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',d2_xboole_0)).

fof(f47,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f40,f45])).

fof(f45,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
