%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0385+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  86 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   16
%              Number of atoms          :   97 ( 244 expanded)
%              Number of equality atoms :   34 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f114,f13])).

fof(f13,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f114,plain,(
    ~ r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f101,f33])).

fof(f33,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f101,plain,(
    ~ r1_tarski(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f12,f100])).

fof(f100,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_setfam_1(sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X4] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | r2_hidden(X4,k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK2(X0,X2),X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X2),X0)
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(sK0)) ),
    inference(resolution,[],[f12,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(X1))
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f43,plain,(
    ~ r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(resolution,[],[f12,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_setfam_1(sK0),X0)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f75,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f12,plain,(
    ~ r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

%------------------------------------------------------------------------------
