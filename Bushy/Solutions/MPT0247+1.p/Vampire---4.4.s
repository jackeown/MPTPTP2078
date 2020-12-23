%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t42_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 521 expanded)
%              Number of leaves         :    3 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :  167 (3754 expanded)
%              Number of equality atoms :  123 (2982 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f89])).

fof(f89,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f25,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( k2_tarski(sK1,sK2) != sK0
        & k1_tarski(sK2) != sK0
        & k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) )
    & ( k2_tarski(sK1,sK2) = sK0
      | k1_tarski(sK2) = sK0
      | k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( k2_tarski(sK1,sK2) != sK0
          & k1_tarski(sK2) != sK0
          & k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) )
      & ( k2_tarski(sK1,sK2) = sK0
        | k1_tarski(sK2) = sK0
        | k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t42_zfmisc_1.p',t42_zfmisc_1)).

fof(f63,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f26,plain,
    ( k1_tarski(sK1) != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f27,f54])).

fof(f54,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f49,f53])).

fof(f53,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f46,f39])).

fof(f39,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t42_zfmisc_1.p',l45_zfmisc_1)).

fof(f24,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k2_tarski(sK1,sK2) != sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f39])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k2_tarski(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,
    ( r1_tarski(sK0,sK0)
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f39])).

fof(f35,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,
    ( k1_tarski(sK2) != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X4] :
      ( r1_tarski(sK0,k2_tarski(sK1,X4))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f37,f72])).

fof(f72,plain,
    ( k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f61,f64])).

fof(f61,plain,(
    ! [X5] :
      ( r1_tarski(sK0,k2_tarski(X5,sK2))
      | k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f36,f54])).

fof(f36,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f122,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f89,f25])).
%------------------------------------------------------------------------------
