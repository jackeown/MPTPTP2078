%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:28 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 158 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   21
%              Number of atoms          :  167 ( 341 expanded)
%              Number of equality atoms :   41 ( 122 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f137,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f136,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f71,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k1_setfam_1(X0)) ) ),
    inference(resolution,[],[f96,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1,X9] : r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1,X9] :
      ( r2_hidden(X9,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9) != X8 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X7 != X9
      | r2_hidden(X9,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f136,plain,(
    ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f135,f71])).

fof(f135,plain,
    ( ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f134,f34])).

fof(f134,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f133,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f133,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f132,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f132,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f131,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f129,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

% (18338)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f129,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f128,f28])).

fof(f128,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f127,f25])).

fof(f127,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f126,f29])).

fof(f126,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f67,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f67,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f26,f66,f66])).

fof(f26,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (18334)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.51  % (18317)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.19/0.51  % (18323)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.51  % (18336)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.51  % (18316)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.52  % (18328)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.19/0.52  % (18336)Refutation not found, incomplete strategy% (18336)------------------------------
% 1.19/0.52  % (18336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (18342)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.19/0.52  % (18320)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.52  % (18336)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (18336)Memory used [KB]: 10746
% 1.19/0.53  % (18336)Time elapsed: 0.073 s
% 1.19/0.53  % (18336)------------------------------
% 1.19/0.53  % (18336)------------------------------
% 1.30/0.53  % (18313)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (18331)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.53  % (18314)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.53  % (18331)Refutation not found, incomplete strategy% (18331)------------------------------
% 1.30/0.53  % (18331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (18331)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (18331)Memory used [KB]: 10618
% 1.30/0.53  % (18331)Time elapsed: 0.129 s
% 1.30/0.53  % (18331)------------------------------
% 1.30/0.53  % (18331)------------------------------
% 1.30/0.53  % (18320)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % (18341)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.53  % (18334)Refutation not found, incomplete strategy% (18334)------------------------------
% 1.30/0.53  % (18334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (18334)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (18334)Memory used [KB]: 10746
% 1.30/0.53  % (18334)Time elapsed: 0.125 s
% 1.30/0.53  % (18334)------------------------------
% 1.30/0.53  % (18334)------------------------------
% 1.30/0.53  % (18318)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f145,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(subsumption_resolution,[],[f137,f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    v1_relat_1(sK2)),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,negated_conjecture,(
% 1.30/0.54    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.30/0.54    inference(negated_conjecture,[],[f15])).
% 1.30/0.54  fof(f15,conjecture,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.30/0.54  fof(f137,plain,(
% 1.30/0.54    ~v1_relat_1(sK2)),
% 1.30/0.54    inference(resolution,[],[f136,f98])).
% 1.30/0.54  fof(f98,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0))) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(resolution,[],[f71,f97])).
% 1.30/0.54  fof(f97,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_relat_1(X1) | v1_relat_1(k1_setfam_1(X0))) )),
% 1.30/0.54    inference(resolution,[],[f96,f34])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.30/0.54  fof(f96,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(resolution,[],[f30,f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f20])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,axiom,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1,X9] : (r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9))) )),
% 1.30/0.54    inference(equality_resolution,[],[f70])).
% 1.30/0.54  fof(f70,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X8,X5,X3,X1,X9] : (r2_hidden(X9,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9) != X8) )),
% 1.30/0.54    inference(equality_resolution,[],[f60])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X7 != X9 | r2_hidden(X9,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.30/0.54    inference(cnf_transformation,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.30/0.54    inference(ennf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 1.30/0.54  fof(f136,plain,(
% 1.30/0.54    ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.30/0.54    inference(subsumption_resolution,[],[f135,f71])).
% 1.30/0.54  fof(f135,plain,(
% 1.30/0.54    ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.30/0.54    inference(resolution,[],[f134,f34])).
% 1.30/0.54  fof(f134,plain,(
% 1.30/0.54    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.30/0.54    inference(subsumption_resolution,[],[f133,f68])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f31,f66])).
% 1.30/0.54  fof(f66,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f32,f65])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f33,f64])).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f37,f63])).
% 1.30/0.54  fof(f63,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f39,f62])).
% 1.30/0.54  fof(f62,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f40,f61])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f41,f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.30/0.54  fof(f39,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.30/0.54  fof(f133,plain,(
% 1.30/0.54    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f132,f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    v1_relat_1(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f132,plain,(
% 1.30/0.54    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f131,f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    v1_relat_1(sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f131,plain,(
% 1.30/0.54    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f130])).
% 1.30/0.54  fof(f130,plain,(
% 1.30/0.54    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.30/0.54    inference(resolution,[],[f129,f29])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,axiom,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 1.30/0.54  % (18338)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  fof(f129,plain,(
% 1.30/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.30/0.54    inference(subsumption_resolution,[],[f128,f28])).
% 1.30/0.54  fof(f128,plain,(
% 1.30/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.30/0.54    inference(subsumption_resolution,[],[f127,f25])).
% 1.30/0.54  fof(f127,plain,(
% 1.30/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.30/0.54    inference(resolution,[],[f126,f29])).
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.30/0.54    inference(resolution,[],[f67,f69])).
% 1.30/0.54  fof(f69,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f38,f66])).
% 1.30/0.54  fof(f38,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.30/0.54    inference(flattening,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.30/0.54    inference(definition_unfolding,[],[f26,f66,f66])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (18320)------------------------------
% 1.30/0.54  % (18320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (18320)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (18320)Memory used [KB]: 6268
% 1.30/0.54  % (18320)Time elapsed: 0.093 s
% 1.30/0.54  % (18320)------------------------------
% 1.30/0.54  % (18320)------------------------------
% 1.30/0.54  % (18321)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.54  % (18343)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.54  % (18315)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (18310)Success in time 0.18 s
%------------------------------------------------------------------------------
