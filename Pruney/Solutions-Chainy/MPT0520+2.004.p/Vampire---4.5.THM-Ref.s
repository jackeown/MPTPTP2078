%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 (1403 expanded)
%              Number of leaves         :   11 ( 388 expanded)
%              Depth                    :   26
%              Number of atoms          :  190 (5437 expanded)
%              Number of equality atoms :   61 (1469 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1319,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1318,f25])).

fof(f25,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).

% (19784)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f16,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f1318,plain,(
    sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1308,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1308,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f53,f1281])).

fof(f1281,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f1280,f24])).

fof(f24,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1280,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(subsumption_resolution,[],[f1277,f257])).

fof(f257,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f227,f26])).

fof(f227,plain,(
    ! [X6,X7] : ~ r2_hidden(X7,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f71,f195])).

fof(f195,plain,(
    ! [X1] : k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f193,f71])).

fof(f193,plain,(
    ! [X1] :
      ( k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1)
      | r2_hidden(sK2(X1,X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),k2_relat_1(k8_relat_1(k1_xboole_0,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X1] :
      ( k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1)
      | k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1)
      | r2_hidden(sK2(X1,X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),k2_relat_1(k8_relat_1(k1_xboole_0,sK1))) ) ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),X0)
      | k4_xboole_0(X0,X1) = k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) ) ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X1] : ~ r2_hidden(X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))) ),
    inference(subsumption_resolution,[],[f69,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X0,sK1)))
      | r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f45,f49])).

fof(f49,plain,(
    ! [X1] : k2_relat_1(k8_relat_1(X1,sK1)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X1)) ),
    inference(superposition,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),X0)) ),
    inference(resolution,[],[f23,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f44,f61])).

fof(f61,plain,(
    k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(superposition,[],[f49,f26])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1277,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k4_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(sK2(X2,X3,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f1268])).

fof(f1268,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k4_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3)
      | k1_xboole_0 = k4_xboole_0(X2,X3)
      | r2_hidden(sK2(X2,X3,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f392,f37])).

fof(f392,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK2(X2,X3,k1_xboole_0),X4)
      | k1_xboole_0 = k4_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X4) ) ),
    inference(forward_demodulation,[],[f347,f327])).

fof(f327,plain,(
    k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f195,f294])).

fof(f294,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f223,f26])).

fof(f223,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X1) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f195,f195])).

fof(f347,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 = k4_xboole_0(X2,X3)
      | r2_hidden(sK2(X2,X3,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),X4)
      | ~ r1_tarski(X2,X4) ) ),
    inference(backward_demodulation,[],[f182,f327])).

fof(f182,plain,(
    ! [X4,X2,X3] :
      ( k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X2,X3)
      | r2_hidden(sK2(X2,X3,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),X4)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f53,plain,(
    ! [X1] : k2_relat_1(k8_relat_1(X1,sK1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(sK1))) ),
    inference(superposition,[],[f47,f41])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1))) ),
    inference(superposition,[],[f46,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:10:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (19792)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.47  % (19804)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.48  % (19804)Refutation not found, incomplete strategy% (19804)------------------------------
% 0.22/0.48  % (19804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (19804)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (19804)Memory used [KB]: 10746
% 0.22/0.48  % (19804)Time elapsed: 0.075 s
% 0.22/0.48  % (19804)------------------------------
% 0.22/0.48  % (19804)------------------------------
% 0.22/0.51  % (19788)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (19805)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (19792)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (19786)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1319,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f1318,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    sK0 != k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).
% 0.22/0.53  % (19784)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).
% 0.22/0.53  fof(f1318,plain,(
% 0.22/0.53    sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f1308,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f1308,plain,(
% 0.22/0.53    k2_relat_1(k8_relat_1(sK0,sK1)) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f53,f1281])).
% 0.22/0.53  fof(f1281,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_relat_1(sK1))),
% 0.22/0.53    inference(resolution,[],[f1280,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f1280,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f1277,f257])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f227,f26])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ( ! [X6,X7] : (~r2_hidden(X7,k4_xboole_0(X6,X6))) )),
% 0.22/0.53    inference(superposition,[],[f71,f195])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f71])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1) | r2_hidden(sK2(X1,X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),k2_relat_1(k8_relat_1(k1_xboole_0,sK1)))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1) | k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X1,X1) | r2_hidden(sK2(X1,X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),k2_relat_1(k8_relat_1(k1_xboole_0,sK1)))) )),
% 0.22/0.53    inference(resolution,[],[f72,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),X0) | k4_xboole_0(X0,X1) = k2_relat_1(k8_relat_1(k1_xboole_0,sK1))) )),
% 0.22/0.53    inference(resolution,[],[f71,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f69,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(k8_relat_1(X0,sK1))) | r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.22/0.53    inference(superposition,[],[f45,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(k8_relat_1(X1,sK1)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X1))) )),
% 0.22/0.53    inference(superposition,[],[f46,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f30,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f28,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),X0))) )),
% 0.22/0.53    inference(resolution,[],[f23,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f31,f39])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.22/0.53    inference(superposition,[],[f44,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.53    inference(superposition,[],[f49,f26])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f1277,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X3) | r2_hidden(sK2(X2,X3,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f1268])).
% 0.22/0.53  fof(f1268,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X3) | k1_xboole_0 = k4_xboole_0(X2,X3) | r2_hidden(sK2(X2,X3,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f392,f37])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (r2_hidden(sK2(X2,X3,k1_xboole_0),X4) | k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_tarski(X2,X4)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f347,f327])).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),
% 0.22/0.53    inference(backward_demodulation,[],[f195,f294])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.53    inference(superposition,[],[f223,f26])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(X0,X0)) )),
% 0.22/0.53    inference(superposition,[],[f195,f195])).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | r2_hidden(sK2(X2,X3,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),X4) | ~r1_tarski(X2,X4)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f182,f327])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (k2_relat_1(k8_relat_1(k1_xboole_0,sK1)) = k4_xboole_0(X2,X3) | r2_hidden(sK2(X2,X3,k2_relat_1(k8_relat_1(k1_xboole_0,sK1))),X4) | ~r1_tarski(X2,X4)) )),
% 0.22/0.53    inference(resolution,[],[f72,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(k8_relat_1(X1,sK1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(sK1)))) )),
% 0.22/0.53    inference(superposition,[],[f47,f41])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(sK1)))) )),
% 0.22/0.53    inference(superposition,[],[f46,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f27,f29,f29])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (19792)------------------------------
% 0.22/0.53  % (19792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19792)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (19792)Memory used [KB]: 11385
% 0.22/0.53  % (19792)Time elapsed: 0.111 s
% 0.22/0.53  % (19792)------------------------------
% 0.22/0.53  % (19792)------------------------------
% 0.22/0.53  % (19787)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (19783)Success in time 0.17 s
%------------------------------------------------------------------------------
