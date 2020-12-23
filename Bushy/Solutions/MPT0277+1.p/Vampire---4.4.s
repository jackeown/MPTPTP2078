%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t75_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 505 expanded)
%              Number of leaves         :    5 ( 103 expanded)
%              Depth                    :   25
%              Number of atoms          :  190 (3353 expanded)
%              Number of equality atoms :  163 (3130 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f110])).

fof(f110,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f107,f73])).

fof(f73,plain,(
    ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f68,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',t37_xboole_1)).

fof(f68,plain,(
    k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ( k2_tarski(sK1,sK2) != sK0
        & k1_tarski(sK2) != sK0
        & k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 )
    & ( k2_tarski(sK1,sK2) = sK0
      | k1_tarski(sK2) = sK0
      | k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) )
   => ( ( ( k2_tarski(sK1,sK2) != sK0
          & k1_tarski(sK2) != sK0
          & k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 )
      & ( k2_tarski(sK1,sK2) = sK0
        | k1_tarski(sK2) = sK0
        | k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',t75_zfmisc_1)).

fof(f67,plain,
    ( k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f29,plain,
    ( k1_tarski(sK1) != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,
    ( k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f30,plain,
    ( k1_tarski(sK2) != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,
    ( k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k1_tarski(sK2) = sK0 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( sK0 != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k1_tarski(sK2) = sK0 ),
    inference(superposition,[],[f31,f54])).

fof(f54,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k1_tarski(sK2) = sK0 ),
    inference(subsumption_resolution,[],[f53,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',l45_zfmisc_1)).

fof(f53,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k2_tarski(sK1,sK2) = sK0 ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k2_tarski(sK1,sK2) = sK0 ),
    inference(superposition,[],[f40,f27])).

fof(f27,plain,
    ( k4_xboole_0(sK0,k2_tarski(sK1,sK2)) = k1_xboole_0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k2_tarski(sK1,sK2) = sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f31,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | k4_xboole_0(sK0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    ! [X4] :
      ( r1_tarski(sK0,k2_tarski(sK1,X4))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f44,f93])).

fof(f93,plain,
    ( k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f85,f73])).

fof(f85,plain,(
    ! [X5] :
      ( r1_tarski(sK0,k2_tarski(X5,sK2))
      | k1_xboole_0 = sK0
      | k1_tarski(sK1) = sK0 ) ),
    inference(superposition,[],[f43,f78])).

fof(f78,plain,
    ( k1_tarski(sK2) = sK0
    | k1_xboole_0 = sK0
    | k1_tarski(sK1) = sK0 ),
    inference(subsumption_resolution,[],[f76,f60])).

fof(f60,plain,
    ( r1_tarski(sK0,sK0)
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k1_tarski(sK2) = sK0 ),
    inference(superposition,[],[f42,f54])).

fof(f42,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k1_tarski(sK2) = sK0 ),
    inference(superposition,[],[f73,f54])).

fof(f43,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f152,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f120,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',t4_boole)).

fof(f120,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) != k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f110,f28])).
%------------------------------------------------------------------------------
