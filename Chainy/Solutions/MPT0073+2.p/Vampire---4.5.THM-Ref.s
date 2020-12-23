%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0073+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  53 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 148 expanded)
%              Number of equality atoms :   25 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(subsumption_resolution,[],[f464,f454])).

fof(f454,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f403,f259])).

fof(f259,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f403,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f402,f257])).

fof(f257,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f402,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,k2_xboole_0(sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f401,f379])).

fof(f379,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f401,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,k2_xboole_0(sK0,sK0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,k2_xboole_0(sK0,sK0))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f189,f275])).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f142,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f189,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f109])).

fof(f109,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f108])).

fof(f108,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f464,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f455,f271])).

fof(f271,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f455,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f190,f454])).

fof(f190,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f122])).
%------------------------------------------------------------------------------
