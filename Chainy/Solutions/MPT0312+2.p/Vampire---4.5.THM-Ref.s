%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0312+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   27 (  42 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  96 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4074,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f4073])).

fof(f4073,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK16,sK18),k2_zfmisc_1(sK16,sK18)) != k2_zfmisc_1(k2_zfmisc_1(sK16,sK18),k2_zfmisc_1(sK16,sK18)) ),
    inference(forward_demodulation,[],[f4072,f1514])).

fof(f1514,plain,(
    sK18 = k3_xboole_0(sK18,sK19) ),
    inference(unit_resulting_resolution,[],[f699,f750])).

fof(f750,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f448])).

fof(f448,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f699,plain,(
    r1_tarski(sK18,sK19) ),
    inference(cnf_transformation,[],[f585])).

fof(f585,plain,
    ( k2_zfmisc_1(sK16,sK18) != k3_xboole_0(k2_zfmisc_1(sK16,sK19),k2_zfmisc_1(sK17,sK18))
    & r1_tarski(sK18,sK19)
    & r1_tarski(sK16,sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19])],[f422,f584])).

fof(f584,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK16,sK18) != k3_xboole_0(k2_zfmisc_1(sK16,sK19),k2_zfmisc_1(sK17,sK18))
      & r1_tarski(sK18,sK19)
      & r1_tarski(sK16,sK17) ) ),
    introduced(choice_axiom,[])).

fof(f422,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f421])).

fof(f421,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f335])).

fof(f335,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f334])).

fof(f334,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f4072,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK16,sK18),k2_zfmisc_1(sK16,sK18)) != k2_zfmisc_1(k2_zfmisc_1(sK16,k3_xboole_0(sK18,sK19)),k2_zfmisc_1(sK16,k3_xboole_0(sK18,sK19))) ),
    inference(forward_demodulation,[],[f3998,f765])).

fof(f765,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3998,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK16,sK18),k2_zfmisc_1(sK16,sK18)) != k2_zfmisc_1(k2_zfmisc_1(sK16,k3_xboole_0(sK19,sK18)),k2_zfmisc_1(sK16,k3_xboole_0(sK19,sK18))) ),
    inference(backward_demodulation,[],[f3441,f3966])).

fof(f3966,plain,(
    ! [X23,X22] : k3_xboole_0(k2_zfmisc_1(sK16,X22),k2_zfmisc_1(sK17,X23)) = k2_zfmisc_1(sK16,k3_xboole_0(X22,X23)) ),
    inference(superposition,[],[f771,f1111])).

fof(f1111,plain,(
    sK16 = k3_xboole_0(sK16,sK17) ),
    inference(unit_resulting_resolution,[],[f698,f750])).

fof(f698,plain,(
    r1_tarski(sK16,sK17) ),
    inference(cnf_transformation,[],[f585])).

fof(f771,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f333])).

fof(f333,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f3441,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK16,sK18),k2_zfmisc_1(sK16,sK18)) != k2_zfmisc_1(k3_xboole_0(k2_zfmisc_1(sK16,sK19),k2_zfmisc_1(sK17,sK18)),k3_xboole_0(k2_zfmisc_1(sK16,sK19),k2_zfmisc_1(sK17,sK18))) ),
    inference(unit_resulting_resolution,[],[f700,f784])).

fof(f784,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f458])).

fof(f458,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f325])).

fof(f325,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f700,plain,(
    k2_zfmisc_1(sK16,sK18) != k3_xboole_0(k2_zfmisc_1(sK16,sK19),k2_zfmisc_1(sK17,sK18)) ),
    inference(cnf_transformation,[],[f585])).
%------------------------------------------------------------------------------
