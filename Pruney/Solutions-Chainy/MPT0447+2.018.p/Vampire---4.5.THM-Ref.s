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
% DateTime   : Thu Dec  3 12:47:10 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 424 expanded)
%              Number of leaves         :   21 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 ( 877 expanded)
%              Number of equality atoms :   43 ( 287 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9956)Refutation not found, incomplete strategy% (9956)------------------------------
% (9956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f655,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f84,f45,f411,f615,f215])).

% (9956)Termination reason: Refutation not found, incomplete strategy

% (9956)Memory used [KB]: 6140
% (9956)Time elapsed: 0.271 s
fof(f215,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k3_relat_1(sK0))
      | ~ r1_tarski(k1_relat_1(sK0),X5)
      | r1_tarski(X4,X5)
      | ~ r1_tarski(k2_relat_1(sK0),X5) ) ),
    inference(superposition,[],[f120,f130])).

% (9956)------------------------------
% (9956)------------------------------
fof(f130,plain,(
    k3_relat_1(sK0) = k3_tarski(k6_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f77,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f120,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X6,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X3)))
      | ~ r1_tarski(X5,X4)
      | r1_tarski(X6,X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f615,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f584,f394])).

fof(f394,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f393,f84])).

fof(f393,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK0))
      | r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f390,f44])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f390,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,sK1)
      | r1_tarski(X0,k2_relat_1(sK1))
      | ~ r1_tarski(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f182,f42])).

fof(f182,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,sK1)
      | r1_tarski(X3,k2_relat_1(sK1))
      | ~ r1_tarski(X3,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X2,k2_relat_1(X1))
      | ~ r1_tarski(X2,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f48,f64])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f584,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k2_relat_1(sK1))
      | r1_tarski(X7,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f278,f131])).

fof(f131,plain,(
    k3_relat_1(sK1) = k3_tarski(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f77,f43])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f277,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f277,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X0)
      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f142,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))
      | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(superposition,[],[f81,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f75])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f81,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f62,f75,f76,f76,f75])).

fof(f62,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f411,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f384,f84])).

fof(f384,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_relat_1(sK1),X0)
      | r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f375,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | r1_tarski(X1,X0)
      | ~ r1_tarski(k3_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f164,f64])).

fof(f164,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(sK1),X2)
      | ~ r1_tarski(k3_relat_1(sK1),X2) ) ),
    inference(superposition,[],[f82,f131])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f375,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f374,f84])).

fof(f374,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK0))
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f371,f44])).

fof(f371,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,sK1)
      | r1_tarski(X0,k1_relat_1(sK1))
      | ~ r1_tarski(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f174,f42])).

fof(f174,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,sK1)
      | r1_tarski(X3,k1_relat_1(sK1))
      | ~ r1_tarski(X3,k1_relat_1(X2)) ) ),
    inference(resolution,[],[f91,f43])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f47,f64])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:07:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (9973)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (9975)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (9977)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (9961)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (9981)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (9967)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (9965)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (9959)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (9969)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.52/0.57  % (9963)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.52/0.57  % (9958)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.57  % (9956)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.52/0.57  % (9971)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.52/0.57  % (9979)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.52/0.57  % (9980)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.52/0.58  % (9968)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.58  % (9964)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.58  % (9953)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.52/0.58  % (9966)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.59  % (9974)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.66/0.59  % (9972)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.59  % (9976)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.59  % (9955)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.59  % (9982)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.60  % (9960)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.60  % (9970)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.66/0.61  % (9978)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.61  % (9962)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.66/0.61  % (9957)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.66/0.61  % (9954)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.62  % (9954)Refutation not found, incomplete strategy% (9954)------------------------------
% 1.66/0.62  % (9954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (9954)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.63  
% 2.01/0.63  % (9954)Memory used [KB]: 1791
% 2.01/0.63  % (9954)Time elapsed: 0.169 s
% 2.01/0.63  % (9954)------------------------------
% 2.01/0.63  % (9954)------------------------------
% 2.59/0.72  % (9975)Refutation found. Thanks to Tanya!
% 2.59/0.72  % SZS status Theorem for theBenchmark
% 2.59/0.73  % SZS output start Proof for theBenchmark
% 2.59/0.73  % (9956)Refutation not found, incomplete strategy% (9956)------------------------------
% 2.59/0.73  % (9956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.73  fof(f655,plain,(
% 2.59/0.73    $false),
% 2.59/0.73    inference(unit_resulting_resolution,[],[f84,f45,f411,f615,f215])).
% 2.59/0.73  % (9956)Termination reason: Refutation not found, incomplete strategy
% 2.59/0.73  
% 2.59/0.73  % (9956)Memory used [KB]: 6140
% 2.59/0.73  % (9956)Time elapsed: 0.271 s
% 2.59/0.73  fof(f215,plain,(
% 2.59/0.73    ( ! [X4,X5] : (~r1_tarski(X4,k3_relat_1(sK0)) | ~r1_tarski(k1_relat_1(sK0),X5) | r1_tarski(X4,X5) | ~r1_tarski(k2_relat_1(sK0),X5)) )),
% 2.59/0.73    inference(superposition,[],[f120,f130])).
% 2.59/0.73  % (9956)------------------------------
% 2.59/0.73  % (9956)------------------------------
% 2.59/0.74  fof(f130,plain,(
% 2.59/0.74    k3_relat_1(sK0) = k3_tarski(k6_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.59/0.74    inference(resolution,[],[f77,f42])).
% 2.59/0.74  fof(f42,plain,(
% 2.59/0.74    v1_relat_1(sK0)),
% 2.59/0.74    inference(cnf_transformation,[],[f38])).
% 2.59/0.74  fof(f38,plain,(
% 2.59/0.74    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.59/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f37,f36])).
% 2.59/0.74  fof(f36,plain,(
% 2.59/0.74    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.59/0.74    introduced(choice_axiom,[])).
% 2.59/0.74  fof(f37,plain,(
% 2.59/0.74    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.59/0.74    introduced(choice_axiom,[])).
% 2.59/0.74  fof(f24,plain,(
% 2.59/0.74    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.59/0.74    inference(flattening,[],[f23])).
% 2.59/0.74  fof(f23,plain,(
% 2.59/0.74    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.59/0.74    inference(ennf_transformation,[],[f22])).
% 2.59/0.74  fof(f22,negated_conjecture,(
% 2.59/0.74    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.59/0.74    inference(negated_conjecture,[],[f21])).
% 2.59/0.74  fof(f21,conjecture,(
% 2.59/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.59/0.74  fof(f77,plain,(
% 2.59/0.74    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f46,f75])).
% 2.59/0.74  fof(f75,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f52,f74])).
% 2.59/0.74  fof(f74,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f53,f73])).
% 2.59/0.74  fof(f73,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f61,f72])).
% 2.59/0.74  fof(f72,plain,(
% 2.59/0.74    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f66,f71])).
% 2.59/0.74  fof(f71,plain,(
% 2.59/0.74    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f67,f70])).
% 2.59/0.74  fof(f70,plain,(
% 2.59/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f68,f69])).
% 2.59/0.74  fof(f69,plain,(
% 2.59/0.74    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f14])).
% 2.59/0.74  fof(f14,axiom,(
% 2.59/0.74    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.59/0.74  fof(f68,plain,(
% 2.59/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f13])).
% 2.59/0.74  fof(f13,axiom,(
% 2.59/0.74    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.59/0.74  fof(f67,plain,(
% 2.59/0.74    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f12])).
% 2.59/0.74  fof(f12,axiom,(
% 2.59/0.74    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.59/0.74  fof(f66,plain,(
% 2.59/0.74    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f11])).
% 2.59/0.74  fof(f11,axiom,(
% 2.59/0.74    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.59/0.74  fof(f61,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f10])).
% 2.59/0.74  fof(f10,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.59/0.74  fof(f53,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f9])).
% 2.59/0.74  fof(f9,axiom,(
% 2.59/0.74    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.59/0.74  fof(f52,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f15])).
% 2.59/0.74  fof(f15,axiom,(
% 2.59/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.59/0.74  fof(f46,plain,(
% 2.59/0.74    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f25])).
% 2.59/0.74  fof(f25,plain,(
% 2.59/0.74    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.59/0.74    inference(ennf_transformation,[],[f19])).
% 2.59/0.74  fof(f19,axiom,(
% 2.59/0.74    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.59/0.74  fof(f120,plain,(
% 2.59/0.74    ( ! [X6,X4,X5,X3] : (~r1_tarski(X6,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X3))) | ~r1_tarski(X5,X4) | r1_tarski(X6,X4) | ~r1_tarski(X3,X4)) )),
% 2.59/0.74    inference(resolution,[],[f83,f64])).
% 2.59/0.74  fof(f64,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f33])).
% 2.59/0.74  fof(f33,plain,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.59/0.74    inference(flattening,[],[f32])).
% 2.59/0.74  fof(f32,plain,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.59/0.74    inference(ennf_transformation,[],[f5])).
% 2.59/0.74  fof(f5,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.59/0.74  fof(f83,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f65,f75])).
% 2.59/0.74  fof(f65,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f35])).
% 2.59/0.74  fof(f35,plain,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.59/0.74    inference(flattening,[],[f34])).
% 2.59/0.74  fof(f34,plain,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.59/0.74    inference(ennf_transformation,[],[f8])).
% 2.59/0.74  fof(f8,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.59/0.74  fof(f615,plain,(
% 2.59/0.74    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.59/0.74    inference(resolution,[],[f584,f394])).
% 2.59/0.74  fof(f394,plain,(
% 2.59/0.74    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.59/0.74    inference(resolution,[],[f393,f84])).
% 2.59/0.74  fof(f393,plain,(
% 2.59/0.74    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK0)) | r1_tarski(X0,k2_relat_1(sK1))) )),
% 2.59/0.74    inference(subsumption_resolution,[],[f390,f44])).
% 2.59/0.74  fof(f44,plain,(
% 2.59/0.74    r1_tarski(sK0,sK1)),
% 2.59/0.74    inference(cnf_transformation,[],[f38])).
% 2.59/0.74  fof(f390,plain,(
% 2.59/0.74    ( ! [X0] : (~r1_tarski(sK0,sK1) | r1_tarski(X0,k2_relat_1(sK1)) | ~r1_tarski(X0,k2_relat_1(sK0))) )),
% 2.59/0.74    inference(resolution,[],[f182,f42])).
% 2.59/0.74  fof(f182,plain,(
% 2.59/0.74    ( ! [X2,X3] : (~v1_relat_1(X2) | ~r1_tarski(X2,sK1) | r1_tarski(X3,k2_relat_1(sK1)) | ~r1_tarski(X3,k2_relat_1(X2))) )),
% 2.59/0.74    inference(resolution,[],[f94,f43])).
% 2.59/0.74  fof(f43,plain,(
% 2.59/0.74    v1_relat_1(sK1)),
% 2.59/0.74    inference(cnf_transformation,[],[f38])).
% 2.59/0.74  fof(f94,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0) | r1_tarski(X2,k2_relat_1(X1)) | ~r1_tarski(X2,k2_relat_1(X0))) )),
% 2.59/0.74    inference(resolution,[],[f48,f64])).
% 2.59/0.74  fof(f48,plain,(
% 2.59/0.74    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f27])).
% 2.59/0.74  fof(f27,plain,(
% 2.59/0.74    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.74    inference(flattening,[],[f26])).
% 2.59/0.74  fof(f26,plain,(
% 2.59/0.74    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.74    inference(ennf_transformation,[],[f20])).
% 2.59/0.74  fof(f20,axiom,(
% 2.59/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.59/0.74  fof(f584,plain,(
% 2.59/0.74    ( ! [X7] : (~r1_tarski(X7,k2_relat_1(sK1)) | r1_tarski(X7,k3_relat_1(sK1))) )),
% 2.59/0.74    inference(superposition,[],[f278,f131])).
% 2.59/0.74  fof(f131,plain,(
% 2.59/0.74    k3_relat_1(sK1) = k3_tarski(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.59/0.74    inference(resolution,[],[f77,f43])).
% 2.59/0.74  fof(f278,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(subsumption_resolution,[],[f277,f78])).
% 2.59/0.74  fof(f78,plain,(
% 2.59/0.74    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f50,f76])).
% 2.59/0.74  fof(f76,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f51,f74])).
% 2.59/0.74  fof(f51,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f16])).
% 2.59/0.74  fof(f16,axiom,(
% 2.59/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.59/0.74  fof(f50,plain,(
% 2.59/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f4])).
% 2.59/0.74  fof(f4,axiom,(
% 2.59/0.74    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.59/0.74  fof(f277,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (~r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X0) | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(superposition,[],[f142,f79])).
% 2.59/0.74  fof(f79,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f54,f76])).
% 2.59/0.74  fof(f54,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f29])).
% 2.59/0.74  fof(f29,plain,(
% 2.59/0.74    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.59/0.74    inference(ennf_transformation,[],[f6])).
% 2.59/0.74  fof(f6,axiom,(
% 2.59/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.59/0.74  fof(f142,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (~r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 2.59/0.74    inference(superposition,[],[f81,f80])).
% 2.59/0.74  fof(f80,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f55,f75])).
% 2.59/0.74  fof(f55,plain,(
% 2.59/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f30])).
% 2.59/0.74  fof(f30,plain,(
% 2.59/0.74    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.59/0.74    inference(ennf_transformation,[],[f3])).
% 2.59/0.74  fof(f3,axiom,(
% 2.59/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.59/0.74  fof(f81,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 2.59/0.74    inference(definition_unfolding,[],[f62,f75,f76,f76,f75])).
% 2.59/0.74  fof(f62,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 2.59/0.74    inference(cnf_transformation,[],[f7])).
% 2.59/0.74  fof(f7,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 2.59/0.74  fof(f411,plain,(
% 2.59/0.74    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.59/0.74    inference(resolution,[],[f384,f84])).
% 2.59/0.74  fof(f384,plain,(
% 2.59/0.74    ( ! [X0] : (~r1_tarski(k3_relat_1(sK1),X0) | r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.59/0.74    inference(resolution,[],[f375,f176])).
% 2.59/0.74  fof(f176,plain,(
% 2.59/0.74    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | r1_tarski(X1,X0) | ~r1_tarski(k3_relat_1(sK1),X0)) )),
% 2.59/0.74    inference(resolution,[],[f164,f64])).
% 2.59/0.74  fof(f164,plain,(
% 2.59/0.74    ( ! [X2] : (r1_tarski(k1_relat_1(sK1),X2) | ~r1_tarski(k3_relat_1(sK1),X2)) )),
% 2.59/0.74    inference(superposition,[],[f82,f131])).
% 2.59/0.74  fof(f82,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 2.59/0.74    inference(definition_unfolding,[],[f63,f75])).
% 2.59/0.74  fof(f63,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f31])).
% 2.59/0.74  fof(f31,plain,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.59/0.74    inference(ennf_transformation,[],[f2])).
% 2.59/0.74  fof(f2,axiom,(
% 2.59/0.74    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.59/0.74  fof(f375,plain,(
% 2.59/0.74    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.59/0.74    inference(resolution,[],[f374,f84])).
% 2.59/0.74  fof(f374,plain,(
% 2.59/0.74    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 2.59/0.74    inference(subsumption_resolution,[],[f371,f44])).
% 2.59/0.74  fof(f371,plain,(
% 2.59/0.74    ( ! [X0] : (~r1_tarski(sK0,sK1) | r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(X0,k1_relat_1(sK0))) )),
% 2.59/0.74    inference(resolution,[],[f174,f42])).
% 2.59/0.74  fof(f174,plain,(
% 2.59/0.74    ( ! [X2,X3] : (~v1_relat_1(X2) | ~r1_tarski(X2,sK1) | r1_tarski(X3,k1_relat_1(sK1)) | ~r1_tarski(X3,k1_relat_1(X2))) )),
% 2.59/0.74    inference(resolution,[],[f91,f43])).
% 2.59/0.74  fof(f91,plain,(
% 2.59/0.74    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0) | r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) )),
% 2.59/0.74    inference(resolution,[],[f47,f64])).
% 2.59/0.74  fof(f47,plain,(
% 2.59/0.74    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.59/0.74    inference(cnf_transformation,[],[f27])).
% 2.59/0.74  fof(f45,plain,(
% 2.59/0.74    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.59/0.74    inference(cnf_transformation,[],[f38])).
% 2.59/0.74  fof(f84,plain,(
% 2.59/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.59/0.74    inference(equality_resolution,[],[f57])).
% 2.59/0.74  fof(f57,plain,(
% 2.59/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.59/0.74    inference(cnf_transformation,[],[f40])).
% 2.59/0.74  fof(f40,plain,(
% 2.59/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.74    inference(flattening,[],[f39])).
% 2.59/0.74  fof(f39,plain,(
% 2.59/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.74    inference(nnf_transformation,[],[f1])).
% 2.59/0.74  fof(f1,axiom,(
% 2.59/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.59/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.59/0.74  % SZS output end Proof for theBenchmark
% 2.59/0.74  % (9975)------------------------------
% 2.59/0.74  % (9975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.74  % (9975)Termination reason: Refutation
% 2.59/0.74  
% 2.59/0.74  % (9975)Memory used [KB]: 7547
% 2.59/0.74  % (9975)Time elapsed: 0.291 s
% 2.59/0.74  % (9975)------------------------------
% 2.59/0.74  % (9975)------------------------------
% 2.59/0.74  % (9952)Success in time 0.36 s
%------------------------------------------------------------------------------
