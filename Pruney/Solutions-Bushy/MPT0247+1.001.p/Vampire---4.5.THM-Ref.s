%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0247+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 242 expanded)
%              Number of leaves         :    2 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :   99 ( 909 expanded)
%              Number of equality atoms :   71 ( 707 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(resolution,[],[f81,f76])).

fof(f76,plain,(
    ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(backward_demodulation,[],[f7,f74])).

fof(f74,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f68,f58])).

fof(f58,plain,
    ( sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f22,f19])).

fof(f19,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    inference(inner_rewriting,[],[f6])).

fof(f6,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f57,plain,
    ( sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( sK0 != sK0
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( sK0 != sK0
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f41,f20])).

fof(f20,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f10,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f39,f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 != k2_tarski(sK1,sK2) ),
    inference(inner_rewriting,[],[f9])).

fof(f9,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,
    ( r1_tarski(sK0,sK0)
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f34,f23])).

fof(f34,plain,
    ( r1_tarski(sK0,sK0)
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f16,f20])).

fof(f16,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,
    ( sK0 = k1_tarski(sK1)
    | sK0 != k1_tarski(sK2) ),
    inference(resolution,[],[f65,f8])).

fof(f8,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X5] :
      ( r1_tarski(sK0,k2_tarski(X5,sK2))
      | sK0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f17,f58])).

fof(f17,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X4] : r1_tarski(sK0,k2_tarski(sK1,X4)) ),
    inference(superposition,[],[f18,f74])).

fof(f18,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
