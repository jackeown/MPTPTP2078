%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:01 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 341 expanded)
%              Number of leaves         :   24 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  309 ( 732 expanded)
%              Number of equality atoms :   82 ( 312 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f626,f189])).

fof(f189,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f188,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f188,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f187,f46])).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f187,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f186,f87])).

fof(f87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f85,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f186,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f180,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f180,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f166,f47])).

fof(f47,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f166,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | v1_xboole_0(k5_relat_1(X1,X2))
      | ~ v1_xboole_0(k1_relat_1(X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f164,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f164,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(k1_relat_1(X1))
      | v1_xboole_0(k5_relat_1(X1,X2))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f160,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f160,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(k1_relat_1(X3))
      | v1_xboole_0(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f155,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f155,plain,(
    ! [X3] :
      ( v1_xboole_0(X3)
      | ~ v1_xboole_0(k1_relat_1(X3))
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f62,f111])).

fof(f111,plain,(
    ! [X1] :
      ( k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) = X1
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f83,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f59,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f73,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f626,plain,(
    ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f619,f43])).

fof(f619,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f613,f339])).

fof(f339,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f338,f49])).

fof(f338,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f337,f47])).

fof(f337,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f336,f87])).

fof(f336,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f335,f43])).

fof(f335,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f333,f46])).

fof(f333,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f223,f92])).

fof(f92,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_xboole_0(k5_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f54,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f46,f55])).

fof(f223,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f222,f49])).

fof(f222,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f221,f46])).

fof(f221,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f220,f87])).

fof(f220,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f219,f43])).

fof(f219,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f210,f47])).

fof(f210,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f44,f89])).

fof(f89,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k2_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(X3),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k5_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f53,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f47,f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f44,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f613,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f612,f45])).

fof(f612,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f611,f47])).

fof(f611,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f610,f87])).

fof(f610,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f603,f49])).

fof(f603,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f331,f46])).

fof(f331,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(k1_relat_1(X9),k2_relat_1(X8))
      | ~ v1_xboole_0(k2_relat_1(X9))
      | v1_xboole_0(k5_relat_1(X8,X9))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f319,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f319,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(k5_relat_1(X8,X9))
      | ~ v1_xboole_0(k2_relat_1(X9))
      | ~ r1_tarski(k1_relat_1(X9),k2_relat_1(X8))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X8,X9)),k2_relat_1(X9))) ) ),
    inference(superposition,[],[f61,f134])).

fof(f134,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3))
      | ~ r1_tarski(k1_relat_1(X3),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3))) ) ),
    inference(superposition,[],[f105,f83])).

fof(f105,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))))
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f99,f63])).

fof(f99,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f74,f53])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5231)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (5223)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (5231)Refutation not found, incomplete strategy% (5231)------------------------------
% 0.22/0.52  % (5231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5231)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5231)Memory used [KB]: 6140
% 0.22/0.52  % (5231)Time elapsed: 0.094 s
% 0.22/0.52  % (5231)------------------------------
% 0.22/0.52  % (5231)------------------------------
% 0.22/0.53  % (5221)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (5230)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (5233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (5239)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (5238)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (5226)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (5241)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (5238)Refutation not found, incomplete strategy% (5238)------------------------------
% 0.22/0.53  % (5238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5238)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5238)Memory used [KB]: 10618
% 0.22/0.53  % (5238)Time elapsed: 0.082 s
% 0.22/0.53  % (5238)------------------------------
% 0.22/0.53  % (5238)------------------------------
% 0.22/0.54  % (5229)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (5242)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (5217)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (5245)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (5222)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (5243)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (5234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (5244)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (5219)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (5218)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (5240)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (5225)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (5218)Refutation not found, incomplete strategy% (5218)------------------------------
% 0.22/0.55  % (5218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5218)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5218)Memory used [KB]: 10618
% 0.22/0.55  % (5218)Time elapsed: 0.124 s
% 0.22/0.55  % (5218)------------------------------
% 0.22/0.55  % (5218)------------------------------
% 0.22/0.55  % (5235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (5233)Refutation not found, incomplete strategy% (5233)------------------------------
% 0.22/0.55  % (5233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5233)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5233)Memory used [KB]: 10618
% 0.22/0.55  % (5233)Time elapsed: 0.124 s
% 0.22/0.55  % (5233)------------------------------
% 0.22/0.55  % (5233)------------------------------
% 0.22/0.55  % (5237)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (5236)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (5227)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (5232)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (5216)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (5228)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.57  % (5224)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.57  % (5224)Refutation not found, incomplete strategy% (5224)------------------------------
% 1.49/0.57  % (5224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (5224)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (5224)Memory used [KB]: 10618
% 1.49/0.57  % (5224)Time elapsed: 0.149 s
% 1.49/0.57  % (5224)------------------------------
% 1.49/0.57  % (5224)------------------------------
% 1.66/0.60  % (5245)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f633,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(unit_resulting_resolution,[],[f43,f626,f189])).
% 1.66/0.60  fof(f189,plain,(
% 1.66/0.60    ( ! [X0] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f188,f45])).
% 1.66/0.60  fof(f45,plain,(
% 1.66/0.60    v1_xboole_0(k1_xboole_0)),
% 1.66/0.60    inference(cnf_transformation,[],[f1])).
% 1.66/0.60  fof(f1,axiom,(
% 1.66/0.60    v1_xboole_0(k1_xboole_0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.66/0.60  fof(f188,plain,(
% 1.66/0.60    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f187,f46])).
% 1.66/0.60  fof(f46,plain,(
% 1.66/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.66/0.60    inference(cnf_transformation,[],[f20])).
% 1.66/0.60  fof(f20,axiom,(
% 1.66/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.66/0.60  fof(f187,plain,(
% 1.66/0.60    ( ! [X0] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f186,f87])).
% 1.66/0.60  fof(f87,plain,(
% 1.66/0.60    v1_relat_1(k1_xboole_0)),
% 1.66/0.60    inference(resolution,[],[f85,f57])).
% 1.66/0.60  fof(f57,plain,(
% 1.66/0.60    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f42])).
% 1.66/0.60  fof(f42,plain,(
% 1.66/0.60    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f41,f40])).
% 1.66/0.60  fof(f40,plain,(
% 1.66/0.60    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f41,plain,(
% 1.66/0.60    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f39,plain,(
% 1.66/0.60    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.66/0.60    inference(rectify,[],[f38])).
% 1.66/0.60  fof(f38,plain,(
% 1.66/0.60    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.66/0.60    inference(nnf_transformation,[],[f30])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,axiom,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.66/0.60  fof(f85,plain,(
% 1.66/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.66/0.60    inference(resolution,[],[f75,f48])).
% 1.66/0.60  fof(f48,plain,(
% 1.66/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f5])).
% 1.66/0.60  fof(f5,axiom,(
% 1.66/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.66/0.60  fof(f75,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f64,f72])).
% 1.66/0.60  fof(f72,plain,(
% 1.66/0.60    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f51,f70])).
% 1.66/0.60  fof(f70,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f60,f69])).
% 1.66/0.60  fof(f69,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f65,f68])).
% 1.66/0.60  fof(f68,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f66,f67])).
% 1.66/0.60  fof(f67,plain,(
% 1.66/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f10,axiom,(
% 1.66/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.66/0.60  fof(f66,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f9])).
% 1.66/0.60  fof(f9,axiom,(
% 1.66/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.66/0.60  fof(f65,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f8])).
% 1.66/0.60  fof(f8,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.66/0.60  fof(f60,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f7])).
% 1.66/0.60  fof(f7,axiom,(
% 1.66/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.60  fof(f51,plain,(
% 1.66/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f6])).
% 1.66/0.60  fof(f6,axiom,(
% 1.66/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.60  fof(f64,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f35])).
% 1.66/0.60  fof(f35,plain,(
% 1.66/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f13])).
% 1.66/0.60  fof(f13,axiom,(
% 1.66/0.60    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.66/0.60  fof(f186,plain,(
% 1.66/0.60    ( ! [X0] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f180,f49])).
% 1.66/0.60  fof(f49,plain,(
% 1.66/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f4])).
% 1.66/0.60  fof(f4,axiom,(
% 1.66/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.66/0.60  fof(f180,plain,(
% 1.66/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.66/0.60    inference(superposition,[],[f166,f47])).
% 1.66/0.60  fof(f47,plain,(
% 1.66/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.66/0.60    inference(cnf_transformation,[],[f20])).
% 1.66/0.60  fof(f166,plain,(
% 1.66/0.60    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | v1_xboole_0(k5_relat_1(X1,X2)) | ~v1_xboole_0(k1_relat_1(X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f164,f63])).
% 1.66/0.60  fof(f63,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f34])).
% 1.66/0.60  fof(f34,plain,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(flattening,[],[f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f16])).
% 1.66/0.60  fof(f16,axiom,(
% 1.66/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.66/0.60  fof(f164,plain,(
% 1.66/0.60    ( ! [X2,X1] : (~v1_xboole_0(k1_relat_1(X1)) | v1_xboole_0(k5_relat_1(X1,X2)) | ~v1_relat_1(k5_relat_1(X1,X2)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(superposition,[],[f160,f54])).
% 1.66/0.60  fof(f54,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f28])).
% 1.66/0.60  fof(f28,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(flattening,[],[f27])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f18])).
% 1.66/0.60  fof(f18,axiom,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.66/0.60  fof(f160,plain,(
% 1.66/0.60    ( ! [X3] : (~v1_xboole_0(k1_relat_1(X3)) | v1_xboole_0(X3) | ~v1_relat_1(X3)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f155,f62])).
% 1.66/0.60  fof(f62,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f32])).
% 1.66/0.60  fof(f32,plain,(
% 1.66/0.60    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f12])).
% 1.66/0.60  fof(f12,axiom,(
% 1.66/0.60    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.66/0.60  fof(f155,plain,(
% 1.66/0.60    ( ! [X3] : (v1_xboole_0(X3) | ~v1_xboole_0(k1_relat_1(X3)) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3))) | ~v1_relat_1(X3)) )),
% 1.66/0.60    inference(superposition,[],[f62,f111])).
% 1.66/0.60  fof(f111,plain,(
% 1.66/0.60    ( ! [X1] : (k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) = X1 | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(superposition,[],[f83,f74])).
% 1.66/0.60  fof(f74,plain,(
% 1.66/0.60    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f52,f71])).
% 1.66/0.60  fof(f71,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f59,f70])).
% 1.66/0.60  fof(f59,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f14])).
% 1.66/0.60  fof(f14,axiom,(
% 1.66/0.60    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.66/0.60  fof(f52,plain,(
% 1.66/0.60    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f24])).
% 1.66/0.60  fof(f24,plain,(
% 1.66/0.60    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f17])).
% 1.66/0.60  fof(f17,axiom,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.66/0.60  fof(f83,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) = X0 | ~v1_xboole_0(X0)) )),
% 1.66/0.60    inference(superposition,[],[f73,f55])).
% 1.66/0.60  fof(f55,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f29])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.66/0.60  fof(f73,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.66/0.60    inference(definition_unfolding,[],[f50,f71])).
% 1.66/0.60  fof(f50,plain,(
% 1.66/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f3])).
% 1.66/0.60  fof(f3,axiom,(
% 1.66/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.66/0.60  fof(f626,plain,(
% 1.66/0.60    ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f619,f43])).
% 1.66/0.60  fof(f619,plain,(
% 1.66/0.60    ~v1_relat_1(sK0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(resolution,[],[f613,f339])).
% 1.66/0.60  fof(f339,plain,(
% 1.66/0.60    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f338,f49])).
% 1.66/0.60  fof(f338,plain,(
% 1.66/0.60    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(forward_demodulation,[],[f337,f47])).
% 1.66/0.60  fof(f337,plain,(
% 1.66/0.60    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f336,f87])).
% 1.66/0.60  fof(f336,plain,(
% 1.66/0.60    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f335,f43])).
% 1.66/0.60  fof(f335,plain,(
% 1.66/0.60    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f333,f46])).
% 1.66/0.60  fof(f333,plain,(
% 1.66/0.60    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.66/0.60    inference(superposition,[],[f223,f92])).
% 1.66/0.60  fof(f92,plain,(
% 1.66/0.60    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_xboole_0(k5_relat_1(X2,X3))) )),
% 1.66/0.60    inference(superposition,[],[f54,f78])).
% 1.66/0.60  fof(f78,plain,(
% 1.66/0.60    ( ! [X0] : (k1_relat_1(X0) = X0 | ~v1_xboole_0(X0)) )),
% 1.66/0.60    inference(superposition,[],[f46,f55])).
% 1.66/0.60  fof(f223,plain,(
% 1.66/0.60    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f222,f49])).
% 1.66/0.60  fof(f222,plain,(
% 1.66/0.60    ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.66/0.60    inference(forward_demodulation,[],[f221,f46])).
% 1.66/0.60  fof(f221,plain,(
% 1.66/0.60    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f220,f87])).
% 1.66/0.60  fof(f220,plain,(
% 1.66/0.60    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f219,f43])).
% 1.66/0.60  fof(f219,plain,(
% 1.66/0.60    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f210,f47])).
% 1.66/0.60  fof(f210,plain,(
% 1.66/0.60    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.66/0.60    inference(superposition,[],[f44,f89])).
% 1.66/0.60  fof(f89,plain,(
% 1.66/0.60    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k2_relat_1(X3) | ~r1_tarski(k1_relat_1(X3),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_xboole_0(k5_relat_1(X2,X3))) )),
% 1.66/0.60    inference(superposition,[],[f53,f77])).
% 1.66/0.60  fof(f77,plain,(
% 1.66/0.60    ( ! [X0] : (k2_relat_1(X0) = X0 | ~v1_xboole_0(X0)) )),
% 1.66/0.60    inference(superposition,[],[f47,f55])).
% 1.66/0.60  fof(f53,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f26])).
% 1.66/0.60  fof(f26,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(flattening,[],[f25])).
% 1.66/0.60  fof(f25,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f19])).
% 1.66/0.60  fof(f19,axiom,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 1.66/0.60  fof(f44,plain,(
% 1.66/0.60    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f37])).
% 1.66/0.60  fof(f37,plain,(
% 1.66/0.60    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).
% 1.66/0.60  fof(f36,plain,(
% 1.66/0.60    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f23,plain,(
% 1.66/0.60    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f22])).
% 1.66/0.60  fof(f22,negated_conjecture,(
% 1.66/0.60    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.66/0.60    inference(negated_conjecture,[],[f21])).
% 1.66/0.60  fof(f21,conjecture,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.66/0.60  fof(f613,plain,(
% 1.66/0.60    ( ! [X0] : (v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f612,f45])).
% 1.66/0.60  fof(f612,plain,(
% 1.66/0.60    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f611,f47])).
% 1.66/0.60  fof(f611,plain,(
% 1.66/0.60    ( ! [X0] : (~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f610,f87])).
% 1.66/0.60  fof(f610,plain,(
% 1.66/0.60    ( ! [X0] : (~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f603,f49])).
% 1.66/0.60  fof(f603,plain,(
% 1.66/0.60    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.66/0.60    inference(superposition,[],[f331,f46])).
% 1.66/0.60  fof(f331,plain,(
% 1.66/0.60    ( ! [X8,X9] : (~r1_tarski(k1_relat_1(X9),k2_relat_1(X8)) | ~v1_xboole_0(k2_relat_1(X9)) | v1_xboole_0(k5_relat_1(X8,X9)) | ~v1_relat_1(X8) | ~v1_relat_1(X9)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f319,f61])).
% 1.66/0.60  fof(f61,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f31])).
% 1.66/0.60  fof(f31,plain,(
% 1.66/0.60    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f11])).
% 1.66/0.60  fof(f11,axiom,(
% 1.66/0.60    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.66/0.60  fof(f319,plain,(
% 1.66/0.60    ( ! [X8,X9] : (v1_xboole_0(k5_relat_1(X8,X9)) | ~v1_xboole_0(k2_relat_1(X9)) | ~r1_tarski(k1_relat_1(X9),k2_relat_1(X8)) | ~v1_relat_1(X8) | ~v1_relat_1(X9) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X8,X9)),k2_relat_1(X9)))) )),
% 1.66/0.60    inference(superposition,[],[f61,f134])).
% 1.66/0.60  fof(f134,plain,(
% 1.66/0.60    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3)) | ~r1_tarski(k1_relat_1(X3),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3)))) )),
% 1.66/0.60    inference(superposition,[],[f105,f83])).
% 1.66/0.60  fof(f105,plain,(
% 1.66/0.60    ( ! [X2,X1] : (k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f99,f63])).
% 1.66/0.60  fof(f99,plain,(
% 1.66/0.60    ( ! [X2,X1] : (k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))) | ~v1_relat_1(k5_relat_1(X1,X2)) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 1.66/0.60    inference(superposition,[],[f74,f53])).
% 1.66/0.60  fof(f43,plain,(
% 1.66/0.60    v1_relat_1(sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f37])).
% 1.66/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (5245)------------------------------
% 1.66/0.60  % (5245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (5245)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (5245)Memory used [KB]: 2174
% 1.66/0.60  % (5245)Time elapsed: 0.183 s
% 1.66/0.60  % (5245)------------------------------
% 1.66/0.60  % (5245)------------------------------
% 1.66/0.60  % (5215)Success in time 0.228 s
%------------------------------------------------------------------------------
