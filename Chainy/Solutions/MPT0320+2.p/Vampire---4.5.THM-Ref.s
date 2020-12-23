%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0320+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   36 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1040,f1178])).

fof(f1178,plain,(
    spl20_1 ),
    inference(avatar_contradiction_clause,[],[f1177])).

fof(f1177,plain,
    ( $false
    | spl20_1 ),
    inference(trivial_inequality_removal,[],[f1176])).

fof(f1176,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),sK2))
    | spl20_1 ),
    inference(forward_demodulation,[],[f1175,f727])).

fof(f727,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1175,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2),k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2))
    | spl20_1 ),
    inference(forward_demodulation,[],[f1164,f677])).

fof(f677,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f330])).

fof(f330,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f1164,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_tarski(sK0,sK1),sK2)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)),k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)))
    | spl20_1 ),
    inference(unit_resulting_resolution,[],[f1039,f687])).

fof(f687,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f441])).

fof(f441,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f325])).

fof(f325,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f1039,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))
    | spl20_1 ),
    inference(avatar_component_clause,[],[f1037])).

fof(f1037,plain,
    ( spl20_1
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f1040,plain,(
    ~ spl20_1 ),
    inference(avatar_split_clause,[],[f1024,f1037])).

fof(f1024,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(trivial_inequality_removal,[],[f1023])).

fof(f1023,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(backward_demodulation,[],[f1022,f727])).

fof(f1022,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(backward_demodulation,[],[f656,f678])).

fof(f678,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f330])).

fof(f656,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f570])).

fof(f570,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f429,f569])).

fof(f569,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f429,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f344])).

fof(f344,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f343])).

fof(f343,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
%------------------------------------------------------------------------------
