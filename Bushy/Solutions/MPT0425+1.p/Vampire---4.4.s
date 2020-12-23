%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t57_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 55.85s
% Output     : Refutation 55.85s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 201 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1101,plain,(
    $false ),
    inference(resolution,[],[f1092,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    & ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) )
    & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f54])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK2,k3_tarski(sK0))
      & ! [X3] :
          ( r1_xboole_0(X3,sK2)
          | ~ r2_hidden(X3,sK1) )
      & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t57_setfam_1)).

fof(f1092,plain,(
    r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(resolution,[],[f865,f110])).

fof(f110,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f72,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',commutativity_k3_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t17_xboole_1)).

fof(f865,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_xboole_0(sK2,k3_tarski(sK0)),X2)
      | r1_tarski(sK2,X2) ) ),
    inference(backward_demodulation,[],[f836,f510])).

fof(f510,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1))),X2)
      | r1_tarski(sK2,X2) ) ),
    inference(resolution,[],[f506,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t1_xboole_1)).

fof(f506,plain,(
    r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f504,f74])).

fof(f504,plain,(
    r1_tarski(sK2,k3_xboole_0(k3_tarski(k2_xboole_0(sK0,sK1)),sK2)) ),
    inference(resolution,[],[f288,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f72,f70])).

fof(f70,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',idempotence_k3_xboole_0)).

fof(f288,plain,(
    ! [X12] :
      ( ~ r1_tarski(sK2,X12)
      | r1_tarski(sK2,k3_xboole_0(k3_tarski(k2_xboole_0(sK0,sK1)),X12)) ) ),
    inference(resolution,[],[f91,f62])).

fof(f62,plain,(
    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t19_xboole_1)).

fof(f836,plain,(
    ! [X0] : k3_xboole_0(sK2,k3_tarski(X0)) = k3_xboole_0(sK2,k3_tarski(k2_xboole_0(X0,sK1))) ),
    inference(superposition,[],[f402,f235])).

fof(f235,plain,(
    ! [X4,X3] : k2_xboole_0(k3_tarski(X4),k3_tarski(X3)) = k3_tarski(k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',commutativity_k2_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t96_zfmisc_1)).

fof(f402,plain,(
    ! [X14] : k3_xboole_0(sK2,X14) = k3_xboole_0(sK2,k2_xboole_0(k3_tarski(sK1),X14)) ),
    inference(forward_demodulation,[],[f382,f99])).

fof(f99,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f73,f66])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t1_boole)).

fof(f382,plain,(
    ! [X14] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X14)) = k3_xboole_0(sK2,k2_xboole_0(k3_tarski(sK1),X14)) ),
    inference(superposition,[],[f88,f198])).

fof(f198,plain,(
    k3_xboole_0(sK2,k3_tarski(sK1)) = k1_xboole_0 ),
    inference(resolution,[],[f197,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',d7_xboole_0)).

fof(f197,plain,(
    r1_xboole_0(sK2,k3_tarski(sK1)) ),
    inference(resolution,[],[f195,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',symmetry_r1_xboole_0)).

fof(f195,plain,(
    r1_xboole_0(k3_tarski(sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | r1_xboole_0(k3_tarski(sK1),sK2) ),
    inference(resolution,[],[f158,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t98_zfmisc_1)).

fof(f158,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK2),sK1)
      | r1_xboole_0(k3_tarski(X0),sK2) ) ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK4(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t23_xboole_1)).
%------------------------------------------------------------------------------
