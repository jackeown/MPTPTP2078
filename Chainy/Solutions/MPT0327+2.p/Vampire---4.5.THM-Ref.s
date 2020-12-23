%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0327+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 104 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1309,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1297,f726])).

% (5454)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
fof(f726,plain,(
    r2_hidden(sK16,sK17) ),
    inference(cnf_transformation,[],[f613])).

fof(f613,plain,
    ( sK17 != k2_xboole_0(k4_xboole_0(sK17,k1_tarski(sK16)),k1_tarski(sK16))
    & r2_hidden(sK16,sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17])],[f438,f612])).

fof(f612,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK17 != k2_xboole_0(k4_xboole_0(sK17,k1_tarski(sK16)),k1_tarski(sK16))
      & r2_hidden(sK16,sK17) ) ),
    introduced(choice_axiom,[])).

fof(f438,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f353])).

fof(f353,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f352])).

fof(f352,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f1297,plain,(
    ~ r2_hidden(sK16,sK17) ),
    inference(resolution,[],[f1296,f1111])).

fof(f1111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f837,f948])).

fof(f948,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f837,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f651])).

fof(f651,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f297])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1296,plain,(
    ~ r1_tarski(k2_tarski(sK16,sK16),sK17) ),
    inference(resolution,[],[f1292,f1224])).

fof(f1224,plain,(
    ! [X0] : sP5(X0,k2_tarski(X0,X0)) ),
    inference(equality_resolution,[],[f1114])).

fof(f1114,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f842,f948])).

fof(f842,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f656])).

fof(f656,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP5(X0,X1) )
      & ( sP5(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f595])).

fof(f595,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP5(X0,X1) ) ),
    inference(definition_folding,[],[f175,f594])).

fof(f594,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1292,plain,(
    ! [X4] :
      ( ~ sP5(sK16,X4)
      | ~ r1_tarski(X4,sK17) ) ),
    inference(trivial_inequality_removal,[],[f1282])).

fof(f1282,plain,(
    ! [X4] :
      ( sK17 != sK17
      | ~ sP5(sK16,X4)
      | ~ r1_tarski(X4,sK17) ) ),
    inference(superposition,[],[f1269,f741])).

fof(f741,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f449])).

fof(f449,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1269,plain,(
    ! [X5] :
      ( sK17 != k2_xboole_0(X5,sK17)
      | ~ sP5(sK16,X5) ) ),
    inference(forward_demodulation,[],[f1268,f825])).

fof(f825,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1268,plain,(
    ! [X5] :
      ( sK17 != k2_xboole_0(X5,k4_xboole_0(sK17,X5))
      | ~ sP5(sK16,X5) ) ),
    inference(forward_demodulation,[],[f1256,f743])).

fof(f743,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1256,plain,(
    ! [X5] :
      ( sK17 != k2_xboole_0(k4_xboole_0(sK17,X5),X5)
      | ~ sP5(sK16,X5) ) ),
    inference(superposition,[],[f1066,f1113])).

fof(f1113,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | ~ sP5(X0,X1) ) ),
    inference(definition_unfolding,[],[f843,f948])).

fof(f843,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f656])).

fof(f1066,plain,(
    sK17 != k2_xboole_0(k4_xboole_0(sK17,k2_tarski(sK16,sK16)),k2_tarski(sK16,sK16)) ),
    inference(definition_unfolding,[],[f727,f948,f948])).

fof(f727,plain,(
    sK17 != k2_xboole_0(k4_xboole_0(sK17,k1_tarski(sK16)),k1_tarski(sK16)) ),
    inference(cnf_transformation,[],[f613])).
%------------------------------------------------------------------------------
