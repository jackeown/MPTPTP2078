%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:55 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   33 (  72 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   17
%              Number of atoms          :   78 ( 199 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f179,f9])).

fof(f9,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
      & r1_setfam_1(X2,k2_tarski(X0,X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_setfam_1(X2,k2_tarski(X0,X1))
       => ! [X3] :
            ~ ( ~ r1_tarski(X3,X1)
              & ~ r1_tarski(X3,X0)
              & r2_hidden(X3,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X2,k2_tarski(X0,X1))
     => ! [X3] :
          ~ ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_setfam_1)).

fof(f179,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f176,f28])).

fof(f28,plain,(
    r1_setfam_1(sK2,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f12,plain,(
    r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f176,plain,(
    ! [X1] :
      ( ~ r1_setfam_1(X1,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
      | ~ r2_hidden(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f175,f10])).

fof(f10,plain,(
    ~ r1_tarski(sK3,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f175,plain,(
    ! [X1] :
      ( r1_tarski(sK3,sK0)
      | ~ r2_hidden(sK3,X1)
      | ~ r1_setfam_1(X1,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ) ),
    inference(superposition,[],[f16,f149])).

fof(f149,plain,(
    sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ),
    inference(subsumption_resolution,[],[f141,f9])).

fof(f141,plain,
    ( ~ r2_hidden(sK3,sK2)
    | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ),
    inference(resolution,[],[f110,f28])).

fof(f110,plain,(
    ! [X1] :
      ( ~ r1_setfam_1(X1,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
      | ~ r2_hidden(sK3,X1)
      | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ) ),
    inference(subsumption_resolution,[],[f108,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f108,plain,(
    ! [X1] :
      ( r1_tarski(sK3,sK1)
      | ~ r2_hidden(sK3,X1)
      | ~ r1_setfam_1(X1,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
      | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ) ),
    inference(superposition,[],[f16,f84])).

fof(f84,plain,
    ( sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3)
    | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ),
    inference(resolution,[],[f71,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f71,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3),k1_tarski(sK0))
    | sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ),
    inference(resolution,[],[f58,f29])).

fof(f58,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3),k1_tarski(sK1))
    | r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3),k1_tarski(sK0)) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f49,plain,(
    r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(resolution,[],[f40,f9])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ) ),
    inference(resolution,[],[f28,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(sK5(X1,X2),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK5(X1,X2))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
