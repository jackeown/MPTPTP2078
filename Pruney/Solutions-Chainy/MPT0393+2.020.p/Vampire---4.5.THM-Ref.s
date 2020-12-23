%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 3.82s
% Output     : Refutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 751 expanded)
%              Number of leaves         :   11 ( 217 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 (1386 expanded)
%              Number of equality atoms :   81 ( 750 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3268,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3203,f686])).

fof(f686,plain,(
    ~ r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f253,f220])).

fof(f220,plain,(
    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f219,f156])).

fof(f156,plain,(
    ~ r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f53,f113,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f113,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f99,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f99,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(unit_resulting_resolution,[],[f80,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f80,plain,(
    ! [X0,X3] : sP6(X3,X3,X0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    sK0 != k1_setfam_1(k1_enumset1(sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f19,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f219,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0))) ),
    inference(subsumption_resolution,[],[f217,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f217,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0))) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0)))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(superposition,[],[f24,f199])).

fof(f199,plain,
    ( sK0 = sK1(k1_enumset1(sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(resolution,[],[f159,f167])).

fof(f167,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_enumset1(X4,X4,X4))
      | X4 = X5 ) ),
    inference(superposition,[],[f74,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f38,f52,f52,f52])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f74,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f159,plain,
    ( r2_hidden(sK1(k1_enumset1(sK0,sK0,sK0),sK0),k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(resolution,[],[f156,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f253,plain,(
    ! [X0] : ~ r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0))) ),
    inference(forward_demodulation,[],[f226,f69])).

fof(f69,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f226,plain,(
    ! [X0] : ~ r2_hidden(k1_setfam_1(k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0))) ),
    inference(backward_demodulation,[],[f105,f220])).

fof(f105,plain,(
    ! [X0] : ~ r2_hidden(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(X0,X0,X0))) ),
    inference(unit_resulting_resolution,[],[f98,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f98,plain,(
    ~ r2_hidden(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f87,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f87,plain,(
    ~ sP6(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f53,f53,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3203,plain,(
    r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f259,f3151])).

fof(f3151,plain,(
    ! [X0] : k1_xboole_0 = k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f347,f358,f1473])).

fof(f1473,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | k1_xboole_0 = k1_enumset1(k1_xboole_0,k1_xboole_0,X2)
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f477,f485])).

fof(f485,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f127,f361])).

fof(f361,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f61,f220])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f52,f52])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f127,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f100,f25])).

fof(f100,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f81,f79])).

fof(f81,plain,(
    ! [X3,X1] : sP6(X3,X1,X3) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f477,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X2,X2,X1)))
      | k1_xboole_0 = k1_enumset1(X2,X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( sP3(X2,X0)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,(
    ! [X4,X2,X3] :
      ( ~ sP3(X2,k1_enumset1(X4,X4,X3))
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f99,f28])).

fof(f28,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f358,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f100,f220])).

fof(f347,plain,(
    ! [X5] : ~ r2_hidden(sK0,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f74,f220])).

fof(f259,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k4_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f233,f69])).

fof(f233,plain,(
    ! [X0] : r2_hidden(k1_setfam_1(k1_xboole_0),k4_xboole_0(k1_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),X0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f123,f220])).

fof(f123,plain,(
    ! [X0] : r2_hidden(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f53,f100,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21325)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (21317)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (21304)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (21307)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (21306)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (21309)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.53  % (21324)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.53  % (21305)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.53  % (21312)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.53  % (21302)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.53  % (21316)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (21303)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (21319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.23/0.53  % (21303)Refutation not found, incomplete strategy% (21303)------------------------------
% 1.23/0.53  % (21303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (21303)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (21303)Memory used [KB]: 1663
% 1.23/0.53  % (21303)Time elapsed: 0.125 s
% 1.23/0.53  % (21303)------------------------------
% 1.23/0.53  % (21303)------------------------------
% 1.23/0.53  % (21316)Refutation not found, incomplete strategy% (21316)------------------------------
% 1.23/0.53  % (21316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (21316)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (21316)Memory used [KB]: 1663
% 1.23/0.53  % (21316)Time elapsed: 0.088 s
% 1.23/0.53  % (21316)------------------------------
% 1.23/0.53  % (21316)------------------------------
% 1.23/0.53  % (21323)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.54  % (21313)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.54  % (21327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.23/0.54  % (21331)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.54  % (21331)Refutation not found, incomplete strategy% (21331)------------------------------
% 1.23/0.54  % (21331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (21331)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (21331)Memory used [KB]: 1663
% 1.23/0.54  % (21331)Time elapsed: 0.128 s
% 1.23/0.54  % (21331)------------------------------
% 1.23/0.54  % (21331)------------------------------
% 1.23/0.54  % (21310)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.54  % (21322)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.54  % (21330)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.54  % (21328)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.23/0.54  % (21318)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.23/0.54  % (21328)Refutation not found, incomplete strategy% (21328)------------------------------
% 1.23/0.54  % (21328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (21328)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (21328)Memory used [KB]: 6140
% 1.23/0.54  % (21328)Time elapsed: 0.126 s
% 1.23/0.54  % (21328)------------------------------
% 1.23/0.54  % (21328)------------------------------
% 1.23/0.54  % (21318)Refutation not found, incomplete strategy% (21318)------------------------------
% 1.23/0.54  % (21318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (21318)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (21318)Memory used [KB]: 10618
% 1.23/0.54  % (21318)Time elapsed: 0.136 s
% 1.23/0.54  % (21318)------------------------------
% 1.23/0.54  % (21318)------------------------------
% 1.23/0.54  % (21326)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.54  % (21314)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.54  % (21320)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.54  % (21326)Refutation not found, incomplete strategy% (21326)------------------------------
% 1.42/0.54  % (21326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (21308)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (21321)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.55  % (21315)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.42/0.55  % (21311)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.55  % (21319)Refutation not found, incomplete strategy% (21319)------------------------------
% 1.42/0.55  % (21319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (21319)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (21319)Memory used [KB]: 1663
% 1.42/0.55  % (21319)Time elapsed: 0.128 s
% 1.42/0.55  % (21319)------------------------------
% 1.42/0.55  % (21319)------------------------------
% 1.42/0.55  % (21329)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.55  % (21329)Refutation not found, incomplete strategy% (21329)------------------------------
% 1.42/0.55  % (21329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (21329)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (21329)Memory used [KB]: 6140
% 1.42/0.55  % (21329)Time elapsed: 0.151 s
% 1.42/0.55  % (21329)------------------------------
% 1.42/0.55  % (21329)------------------------------
% 1.42/0.55  % (21326)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (21326)Memory used [KB]: 10618
% 1.42/0.55  % (21326)Time elapsed: 0.121 s
% 1.42/0.55  % (21326)------------------------------
% 1.42/0.55  % (21326)------------------------------
% 1.42/0.55  % (21320)Refutation not found, incomplete strategy% (21320)------------------------------
% 1.42/0.55  % (21320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (21320)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (21320)Memory used [KB]: 1663
% 1.42/0.55  % (21320)Time elapsed: 0.146 s
% 1.42/0.55  % (21320)------------------------------
% 1.42/0.55  % (21320)------------------------------
% 1.42/0.56  % (21314)Refutation not found, incomplete strategy% (21314)------------------------------
% 1.42/0.56  % (21314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (21314)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (21314)Memory used [KB]: 10618
% 1.42/0.56  % (21314)Time elapsed: 0.152 s
% 1.42/0.56  % (21314)------------------------------
% 1.42/0.56  % (21314)------------------------------
% 1.42/0.63  % (21317)Refutation not found, incomplete strategy% (21317)------------------------------
% 1.42/0.63  % (21317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.63  % (21317)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.63  
% 1.42/0.63  % (21317)Memory used [KB]: 6140
% 1.42/0.63  % (21317)Time elapsed: 0.208 s
% 1.42/0.63  % (21317)------------------------------
% 1.42/0.63  % (21317)------------------------------
% 1.97/0.64  % (21379)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.97/0.64  % (21372)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.97/0.66  % (21305)Refutation not found, incomplete strategy% (21305)------------------------------
% 1.97/0.66  % (21305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (21305)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.66  
% 1.97/0.66  % (21305)Memory used [KB]: 6140
% 1.97/0.66  % (21305)Time elapsed: 0.247 s
% 1.97/0.66  % (21305)------------------------------
% 1.97/0.66  % (21305)------------------------------
% 1.97/0.66  % (21302)Refutation not found, incomplete strategy% (21302)------------------------------
% 1.97/0.66  % (21302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (21302)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.66  
% 1.97/0.66  % (21302)Memory used [KB]: 1663
% 1.97/0.66  % (21302)Time elapsed: 0.251 s
% 1.97/0.66  % (21302)------------------------------
% 1.97/0.66  % (21302)------------------------------
% 1.97/0.67  % (21380)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.97/0.67  % (21377)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.97/0.67  % (21380)Refutation not found, incomplete strategy% (21380)------------------------------
% 1.97/0.67  % (21380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.67  % (21380)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.67  
% 1.97/0.67  % (21380)Memory used [KB]: 10618
% 1.97/0.67  % (21380)Time elapsed: 0.094 s
% 1.97/0.67  % (21380)------------------------------
% 1.97/0.67  % (21380)------------------------------
% 1.97/0.67  % (21377)Refutation not found, incomplete strategy% (21377)------------------------------
% 1.97/0.67  % (21377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.67  % (21377)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.67  
% 1.97/0.67  % (21377)Memory used [KB]: 6140
% 1.97/0.67  % (21377)Time elapsed: 0.099 s
% 1.97/0.67  % (21377)------------------------------
% 1.97/0.67  % (21377)------------------------------
% 1.97/0.68  % (21375)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.97/0.68  % (21385)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.27/0.69  % (21383)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.27/0.69  % (21386)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.27/0.69  % (21388)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.27/0.70  % (21393)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.27/0.72  % (21393)Refutation not found, incomplete strategy% (21393)------------------------------
% 2.27/0.72  % (21393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.72  % (21393)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.72  
% 2.27/0.72  % (21393)Memory used [KB]: 10746
% 2.27/0.72  % (21393)Time elapsed: 0.129 s
% 2.27/0.72  % (21393)------------------------------
% 2.27/0.72  % (21393)------------------------------
% 2.27/0.73  % (21428)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.89/0.81  % (21457)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.89/0.81  % (21463)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.89/0.82  % (21464)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.89/0.82  % (21304)Time limit reached!
% 2.89/0.82  % (21304)------------------------------
% 2.89/0.82  % (21304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.82  % (21304)Termination reason: Time limit
% 2.89/0.82  
% 2.89/0.82  % (21304)Memory used [KB]: 7675
% 2.89/0.82  % (21304)Time elapsed: 0.407 s
% 2.89/0.82  % (21304)------------------------------
% 2.89/0.82  % (21304)------------------------------
% 2.89/0.82  % (21464)Refutation not found, incomplete strategy% (21464)------------------------------
% 2.89/0.82  % (21464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.82  % (21464)Termination reason: Refutation not found, incomplete strategy
% 2.89/0.82  
% 2.89/0.82  % (21464)Memory used [KB]: 10746
% 2.89/0.82  % (21464)Time elapsed: 0.114 s
% 2.89/0.82  % (21464)------------------------------
% 2.89/0.82  % (21464)------------------------------
% 2.89/0.82  % (21485)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.89/0.83  % (21467)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.49/0.95  % (21505)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.49/0.95  % (21485)Refutation not found, incomplete strategy% (21485)------------------------------
% 3.49/0.95  % (21485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.95  % (21485)Termination reason: Refutation not found, incomplete strategy
% 3.49/0.95  
% 3.49/0.95  % (21485)Memory used [KB]: 6140
% 3.49/0.95  % (21485)Time elapsed: 0.206 s
% 3.49/0.96  % (21485)------------------------------
% 3.49/0.96  % (21485)------------------------------
% 3.49/0.96  % (21506)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.49/0.96  % (21308)Time limit reached!
% 3.49/0.96  % (21308)------------------------------
% 3.49/0.96  % (21308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.96  % (21308)Termination reason: Time limit
% 3.49/0.96  % (21308)Termination phase: Saturation
% 3.49/0.96  
% 3.49/0.96  % (21308)Memory used [KB]: 14072
% 3.49/0.96  % (21308)Time elapsed: 0.500 s
% 3.49/0.96  % (21308)------------------------------
% 3.49/0.96  % (21308)------------------------------
% 3.49/0.97  % (21467)Refutation not found, incomplete strategy% (21467)------------------------------
% 3.49/0.97  % (21467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.97  % (21467)Termination reason: Refutation not found, incomplete strategy
% 3.49/0.97  
% 3.49/0.97  % (21467)Memory used [KB]: 6268
% 3.49/0.97  % (21467)Time elapsed: 0.256 s
% 3.49/0.97  % (21467)------------------------------
% 3.49/0.97  % (21467)------------------------------
% 3.82/1.00  % (21321)Refutation found. Thanks to Tanya!
% 3.82/1.00  % SZS status Theorem for theBenchmark
% 3.82/1.01  % SZS output start Proof for theBenchmark
% 3.82/1.01  fof(f3268,plain,(
% 3.82/1.01    $false),
% 3.82/1.01    inference(subsumption_resolution,[],[f3203,f686])).
% 3.82/1.01  fof(f686,plain,(
% 3.82/1.01    ~r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 3.82/1.01    inference(superposition,[],[f253,f220])).
% 3.82/1.01  fof(f220,plain,(
% 3.82/1.01    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 3.82/1.01    inference(subsumption_resolution,[],[f219,f156])).
% 3.82/1.01  fof(f156,plain,(
% 3.82/1.01    ~r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0)))),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f53,f113,f22])).
% 3.82/1.01  fof(f22,plain,(
% 3.82/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.82/1.01    inference(cnf_transformation,[],[f1])).
% 3.82/1.01  fof(f1,axiom,(
% 3.82/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.82/1.01  fof(f113,plain,(
% 3.82/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1)) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f99,f25])).
% 3.82/1.01  fof(f25,plain,(
% 3.82/1.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f17])).
% 3.82/1.01  fof(f17,plain,(
% 3.82/1.01    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 3.82/1.01    inference(ennf_transformation,[],[f10])).
% 3.82/1.01  fof(f10,axiom,(
% 3.82/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 3.82/1.01  fof(f99,plain,(
% 3.82/1.01    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f80,f79])).
% 3.82/1.01  fof(f79,plain,(
% 3.82/1.01    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,k1_enumset1(X0,X0,X1))) )),
% 3.82/1.01    inference(equality_resolution,[],[f65])).
% 3.82/1.01  fof(f65,plain,(
% 3.82/1.01    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.82/1.01    inference(definition_unfolding,[],[f47,f51])).
% 3.82/1.01  fof(f51,plain,(
% 3.82/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f4])).
% 3.82/1.01  fof(f4,axiom,(
% 3.82/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.82/1.01  fof(f47,plain,(
% 3.82/1.01    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 3.82/1.01    inference(cnf_transformation,[],[f2])).
% 3.82/1.01  fof(f2,axiom,(
% 3.82/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 3.82/1.01  fof(f80,plain,(
% 3.82/1.01    ( ! [X0,X3] : (sP6(X3,X3,X0)) )),
% 3.82/1.01    inference(equality_resolution,[],[f45])).
% 3.82/1.01  fof(f45,plain,(
% 3.82/1.01    ( ! [X0,X3,X1] : (X1 != X3 | sP6(X3,X1,X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f2])).
% 3.82/1.01  fof(f53,plain,(
% 3.82/1.01    sK0 != k1_setfam_1(k1_enumset1(sK0,sK0,sK0))),
% 3.82/1.01    inference(definition_unfolding,[],[f19,f52])).
% 3.82/1.01  fof(f52,plain,(
% 3.82/1.01    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.82/1.01    inference(definition_unfolding,[],[f43,f51])).
% 3.82/1.01  fof(f43,plain,(
% 3.82/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f3])).
% 3.82/1.01  fof(f3,axiom,(
% 3.82/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.82/1.01  fof(f19,plain,(
% 3.82/1.01    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 3.82/1.01    inference(cnf_transformation,[],[f14])).
% 3.82/1.01  fof(f14,plain,(
% 3.82/1.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.82/1.01    inference(ennf_transformation,[],[f13])).
% 3.82/1.01  fof(f13,negated_conjecture,(
% 3.82/1.01    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.82/1.01    inference(negated_conjecture,[],[f12])).
% 3.82/1.01  fof(f12,conjecture,(
% 3.82/1.01    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 3.82/1.01  fof(f219,plain,(
% 3.82/1.01    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0)))),
% 3.82/1.01    inference(subsumption_resolution,[],[f217,f66])).
% 3.82/1.01  fof(f66,plain,(
% 3.82/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.82/1.01    inference(equality_resolution,[],[f21])).
% 3.82/1.01  fof(f21,plain,(
% 3.82/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.82/1.01    inference(cnf_transformation,[],[f1])).
% 3.82/1.01  fof(f217,plain,(
% 3.82/1.01    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0)))),
% 3.82/1.01    inference(duplicate_literal_removal,[],[f216])).
% 3.82/1.01  fof(f216,plain,(
% 3.82/1.01    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,sK0))) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 3.82/1.01    inference(superposition,[],[f24,f199])).
% 3.82/1.01  fof(f199,plain,(
% 3.82/1.01    sK0 = sK1(k1_enumset1(sK0,sK0,sK0),sK0) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 3.82/1.01    inference(resolution,[],[f159,f167])).
% 3.82/1.01  fof(f167,plain,(
% 3.82/1.01    ( ! [X4,X5] : (~r2_hidden(X5,k1_enumset1(X4,X4,X4)) | X4 = X5) )),
% 3.82/1.01    inference(superposition,[],[f74,f58])).
% 3.82/1.01  fof(f58,plain,(
% 3.82/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 3.82/1.01    inference(definition_unfolding,[],[f38,f52,f52,f52])).
% 3.82/1.01  fof(f38,plain,(
% 3.82/1.01    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.82/1.01    inference(cnf_transformation,[],[f7])).
% 3.82/1.01  fof(f7,axiom,(
% 3.82/1.01    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 3.82/1.01  fof(f74,plain,(
% 3.82/1.01    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 3.82/1.01    inference(equality_resolution,[],[f55])).
% 3.82/1.01  fof(f55,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 3.82/1.01    inference(definition_unfolding,[],[f36,f52])).
% 3.82/1.01  fof(f36,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.82/1.01    inference(cnf_transformation,[],[f8])).
% 3.82/1.01  fof(f8,axiom,(
% 3.82/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 3.82/1.01  fof(f159,plain,(
% 3.82/1.01    r2_hidden(sK1(k1_enumset1(sK0,sK0,sK0),sK0),k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 3.82/1.01    inference(resolution,[],[f156,f23])).
% 3.82/1.01  fof(f23,plain,(
% 3.82/1.01    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK1(X0,X1),X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f16])).
% 3.82/1.01  fof(f16,plain,(
% 3.82/1.01    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.82/1.01    inference(flattening,[],[f15])).
% 3.82/1.01  fof(f15,plain,(
% 3.82/1.01    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f11])).
% 3.82/1.01  fof(f11,axiom,(
% 3.82/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 3.82/1.01  fof(f24,plain,(
% 3.82/1.01    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 3.82/1.01    inference(cnf_transformation,[],[f16])).
% 3.82/1.01  fof(f253,plain,(
% 3.82/1.01    ( ! [X0] : (~r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)))) )),
% 3.82/1.01    inference(forward_demodulation,[],[f226,f69])).
% 3.82/1.01  fof(f69,plain,(
% 3.82/1.01    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 3.82/1.01    inference(equality_resolution,[],[f68])).
% 3.82/1.01  fof(f68,plain,(
% 3.82/1.01    ( ! [X1] : (k1_xboole_0 = X1 | k1_setfam_1(k1_xboole_0) != X1) )),
% 3.82/1.01    inference(equality_resolution,[],[f34])).
% 3.82/1.01  fof(f34,plain,(
% 3.82/1.01    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = X1 | k1_setfam_1(X0) != X1) )),
% 3.82/1.01    inference(cnf_transformation,[],[f18])).
% 3.82/1.01  fof(f18,plain,(
% 3.82/1.01    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 3.82/1.01    inference(ennf_transformation,[],[f9])).
% 3.82/1.01  fof(f9,axiom,(
% 3.82/1.01    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 3.82/1.01  fof(f226,plain,(
% 3.82/1.01    ( ! [X0] : (~r2_hidden(k1_setfam_1(k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)))) )),
% 3.82/1.01    inference(backward_demodulation,[],[f105,f220])).
% 3.82/1.01  fof(f105,plain,(
% 3.82/1.01    ( ! [X0] : (~r2_hidden(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(X0,X0,X0)))) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f98,f56])).
% 3.82/1.01  fof(f56,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | r2_hidden(X0,X1)) )),
% 3.82/1.01    inference(definition_unfolding,[],[f35,f52])).
% 3.82/1.01  fof(f35,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.82/1.01    inference(cnf_transformation,[],[f8])).
% 3.82/1.01  fof(f98,plain,(
% 3.82/1.01    ~r2_hidden(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f87,f78])).
% 3.82/1.01  fof(f78,plain,(
% 3.82/1.01    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | sP6(X3,X1,X0)) )),
% 3.82/1.01    inference(equality_resolution,[],[f64])).
% 3.82/1.01  fof(f64,plain,(
% 3.82/1.01    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.82/1.01    inference(definition_unfolding,[],[f48,f51])).
% 3.82/1.01  fof(f48,plain,(
% 3.82/1.01    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 3.82/1.01    inference(cnf_transformation,[],[f2])).
% 3.82/1.01  fof(f87,plain,(
% 3.82/1.01    ~sP6(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),sK0,sK0)),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f53,f53,f46])).
% 3.82/1.01  fof(f46,plain,(
% 3.82/1.01    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 3.82/1.01    inference(cnf_transformation,[],[f2])).
% 3.82/1.01  fof(f3203,plain,(
% 3.82/1.01    r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 3.82/1.01    inference(superposition,[],[f259,f3151])).
% 3.82/1.01  fof(f3151,plain,(
% 3.82/1.01    ( ! [X0] : (k1_xboole_0 = k1_enumset1(k1_xboole_0,k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f347,f358,f1473])).
% 3.82/1.01  fof(f1473,plain,(
% 3.82/1.01    ( ! [X2,X3] : (~r2_hidden(X3,k1_xboole_0) | k1_xboole_0 = k1_enumset1(k1_xboole_0,k1_xboole_0,X2) | r2_hidden(X3,X2)) )),
% 3.82/1.01    inference(superposition,[],[f477,f485])).
% 3.82/1.01  fof(f485,plain,(
% 3.82/1.01    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f127,f361])).
% 3.82/1.01  fof(f361,plain,(
% 3.82/1.01    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 3.82/1.01    inference(duplicate_literal_removal,[],[f346])).
% 3.82/1.01  fof(f346,plain,(
% 3.82/1.01    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4 | k1_xboole_0 = X4) )),
% 3.82/1.01    inference(superposition,[],[f61,f220])).
% 3.82/1.01  fof(f61,plain,(
% 3.82/1.01    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 3.82/1.01    inference(definition_unfolding,[],[f40,f52,f52])).
% 3.82/1.01  fof(f40,plain,(
% 3.82/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.82/1.01    inference(cnf_transformation,[],[f6])).
% 3.82/1.01  fof(f6,axiom,(
% 3.82/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 3.82/1.01  fof(f127,plain,(
% 3.82/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f100,f25])).
% 3.82/1.01  fof(f100,plain,(
% 3.82/1.01    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 3.82/1.01    inference(unit_resulting_resolution,[],[f81,f79])).
% 3.82/1.01  fof(f81,plain,(
% 3.82/1.01    ( ! [X3,X1] : (sP6(X3,X1,X3)) )),
% 3.82/1.01    inference(equality_resolution,[],[f44])).
% 3.82/1.01  fof(f44,plain,(
% 3.82/1.01    ( ! [X0,X3,X1] : (X0 != X3 | sP6(X3,X1,X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f2])).
% 3.82/1.01  fof(f477,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) | k1_xboole_0 = k1_enumset1(X2,X2,X1) | r2_hidden(X0,X1)) )),
% 3.82/1.01    inference(resolution,[],[f115,f72])).
% 3.82/1.02  fof(f72,plain,(
% 3.82/1.02    ( ! [X2,X0] : (sP3(X2,X0) | k1_xboole_0 = X0 | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 3.82/1.02    inference(equality_resolution,[],[f30])).
% 3.82/1.02  fof(f30,plain,(
% 3.82/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | sP3(X2,X0) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 3.82/1.02    inference(cnf_transformation,[],[f18])).
% 3.82/1.02  fof(f115,plain,(
% 3.82/1.02    ( ! [X4,X2,X3] : (~sP3(X2,k1_enumset1(X4,X4,X3)) | r2_hidden(X2,X3)) )),
% 3.82/1.02    inference(resolution,[],[f99,f28])).
% 3.82/1.02  fof(f28,plain,(
% 3.82/1.02    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~sP3(X2,X0)) )),
% 3.82/1.02    inference(cnf_transformation,[],[f18])).
% 3.82/1.02  fof(f358,plain,(
% 3.82/1.02    r2_hidden(sK0,k1_xboole_0)),
% 3.82/1.02    inference(superposition,[],[f100,f220])).
% 3.82/1.02  fof(f347,plain,(
% 3.82/1.02    ( ! [X5] : (~r2_hidden(sK0,k4_xboole_0(X5,k1_xboole_0))) )),
% 3.82/1.02    inference(superposition,[],[f74,f220])).
% 3.82/1.02  fof(f259,plain,(
% 3.82/1.02    ( ! [X0] : (r2_hidden(k1_xboole_0,k4_xboole_0(k1_enumset1(k1_xboole_0,k1_xboole_0,X0),k1_xboole_0))) )),
% 3.82/1.02    inference(forward_demodulation,[],[f233,f69])).
% 3.82/1.02  fof(f233,plain,(
% 3.82/1.02    ( ! [X0] : (r2_hidden(k1_setfam_1(k1_xboole_0),k4_xboole_0(k1_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),X0),k1_xboole_0))) )),
% 3.82/1.02    inference(backward_demodulation,[],[f123,f220])).
% 3.82/1.02  fof(f123,plain,(
% 3.82/1.02    ( ! [X0] : (r2_hidden(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k4_xboole_0(k1_enumset1(k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),k1_setfam_1(k1_enumset1(sK0,sK0,sK0)),X0),k1_enumset1(sK0,sK0,sK0)))) )),
% 3.82/1.02    inference(unit_resulting_resolution,[],[f53,f100,f54])).
% 3.82/1.02  fof(f54,plain,(
% 3.82/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 3.82/1.02    inference(definition_unfolding,[],[f37,f52])).
% 3.82/1.02  fof(f37,plain,(
% 3.82/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.82/1.02    inference(cnf_transformation,[],[f8])).
% 3.82/1.02  % SZS output end Proof for theBenchmark
% 3.82/1.02  % (21321)------------------------------
% 3.82/1.02  % (21321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/1.02  % (21321)Termination reason: Refutation
% 3.82/1.02  
% 3.82/1.02  % (21321)Memory used [KB]: 5245
% 3.82/1.02  % (21321)Time elapsed: 0.585 s
% 3.82/1.02  % (21321)------------------------------
% 3.82/1.02  % (21321)------------------------------
% 3.82/1.02  % (21301)Success in time 0.645 s
%------------------------------------------------------------------------------
