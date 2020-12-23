%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t39_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 128 expanded)
%              Number of leaves         :    3 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 569 expanded)
%              Number of equality atoms :   54 ( 380 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(subsumption_resolution,[],[f43,f39])).

fof(f39,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f38,f29])).

fof(f29,plain,
    ( k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t39_zfmisc_1.p',l3_zfmisc_1)).

fof(f21,plain,
    ( k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k1_tarski(sK1)) )
    & ( k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k1_tarski(sK1)) )
      & ( k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t39_zfmisc_1.p',t39_zfmisc_1)).

fof(f38,plain,
    ( k1_tarski(sK1) != sK0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f36,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f27,f29])).

fof(f27,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_tarski(sK1) != sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f23,f29])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,k1_tarski(sK1))
    | k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK1))
    | k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f39,f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
