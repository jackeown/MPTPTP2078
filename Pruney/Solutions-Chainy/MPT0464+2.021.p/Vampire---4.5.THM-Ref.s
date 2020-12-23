%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 344 expanded)
%              Number of leaves         :   22 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  241 ( 558 expanded)
%              Number of equality atoms :   60 ( 286 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(subsumption_resolution,[],[f316,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f316,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f315,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f87,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

% (16435)Refutation not found, incomplete strategy% (16435)------------------------------
% (16435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16435)Termination reason: Refutation not found, incomplete strategy

% (16435)Memory used [KB]: 10746
% (16435)Time elapsed: 0.128 s
% (16435)------------------------------
% (16435)------------------------------
% (16436)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f315,plain,(
    ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f314,f87])).

fof(f314,plain,
    ( ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f313,f40])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f313,plain,
    ( ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f312,f39])).

fof(f312,plain,
    ( ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f311,f250])).

fof(f250,plain,(
    ! [X0,X1] : k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(forward_demodulation,[],[f249,f142])).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f139,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f139,plain,(
    ! [X0] : v1_xboole_0(k5_xboole_0(X0,X0)) ),
    inference(resolution,[],[f138,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_xboole_0(X0,X0),X0)
      | v1_xboole_0(k5_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f134,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f134,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f85,f84])).

fof(f84,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f44,f81])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f81])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f138,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f86,f84])).

% (16438)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f46,f82])).

% (16450)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f249,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(subsumption_resolution,[],[f248,f108])).

fof(f108,plain,(
    ! [X6,X2,X0,X3,X1] : r2_hidden(X6,k4_enumset1(X0,X0,X1,X2,X3,X6)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X6) != X5 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f77,f65])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f248,plain,(
    ! [X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1))
      | ~ r2_hidden(X1,k4_enumset1(X0,X0,X0,X0,X0,X1)) ) ),
    inference(superposition,[],[f93,f84])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2)))
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f62,f80,f82,f80])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f311,plain,
    ( k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f230,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f230,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f226,f108])).

fof(f226,plain,
    ( ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f225,f210])).

fof(f210,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f209,f40])).

fof(f209,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f208,f37])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f208,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f207,f42])).

fof(f207,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f83,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f83,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f38,f81,f81])).

fof(f38,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f225,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f166,f84])).

fof(f166,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k1_setfam_1(X7),k1_setfam_1(k4_enumset1(X8,X8,X8,X8,X8,X6)))
      | ~ r2_hidden(X8,X7)
      | k1_xboole_0 = k4_enumset1(X8,X8,X8,X8,X8,X6)
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:12:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (16441)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (16441)Refutation not found, incomplete strategy% (16441)------------------------------
% 0.22/0.51  % (16441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16451)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (16457)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (16453)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (16449)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (16453)Refutation not found, incomplete strategy% (16453)------------------------------
% 0.22/0.52  % (16453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16453)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16453)Memory used [KB]: 10746
% 0.22/0.53  % (16453)Time elapsed: 0.090 s
% 0.22/0.53  % (16453)------------------------------
% 0.22/0.53  % (16453)------------------------------
% 0.22/0.53  % (16441)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16441)Memory used [KB]: 10746
% 0.22/0.53  % (16441)Time elapsed: 0.092 s
% 0.22/0.53  % (16441)------------------------------
% 0.22/0.53  % (16441)------------------------------
% 0.22/0.53  % (16432)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (16439)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (16440)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (16437)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (16442)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (16459)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (16437)Refutation not found, incomplete strategy% (16437)------------------------------
% 0.22/0.54  % (16437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16437)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16437)Memory used [KB]: 6268
% 0.22/0.54  % (16437)Time elapsed: 0.129 s
% 0.22/0.54  % (16437)------------------------------
% 0.22/0.54  % (16437)------------------------------
% 0.22/0.54  % (16455)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (16448)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (16455)Refutation not found, incomplete strategy% (16455)------------------------------
% 0.22/0.55  % (16455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16455)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16455)Memory used [KB]: 10746
% 0.22/0.55  % (16455)Time elapsed: 0.132 s
% 0.22/0.55  % (16455)------------------------------
% 0.22/0.55  % (16455)------------------------------
% 0.22/0.55  % (16458)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (16447)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (16443)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (16443)Refutation not found, incomplete strategy% (16443)------------------------------
% 0.22/0.55  % (16443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (16443)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (16443)Memory used [KB]: 10618
% 0.22/0.55  % (16443)Time elapsed: 0.111 s
% 0.22/0.55  % (16443)------------------------------
% 0.22/0.55  % (16443)------------------------------
% 0.22/0.55  % (16445)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (16433)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (16456)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (16435)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (16439)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (16446)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f322,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f316,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f22])).
% 0.22/0.56  fof(f22,conjecture,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.56  fof(f316,plain,(
% 0.22/0.56    ~v1_relat_1(sK1)),
% 0.22/0.56    inference(resolution,[],[f315,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f87,f126])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f43,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f47,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f48,f80])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f49,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f56,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f64,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  % (16435)Refutation not found, incomplete strategy% (16435)------------------------------
% 0.22/0.56  % (16435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (16435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (16435)Memory used [KB]: 10746
% 0.22/0.56  % (16435)Time elapsed: 0.128 s
% 0.22/0.56  % (16435)------------------------------
% 0.22/0.56  % (16435)------------------------------
% 0.22/0.56  % (16436)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f314,f87])).
% 0.22/0.56  fof(f314,plain,(
% 0.22/0.56    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f313,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    v1_relat_1(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f312,f39])).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f311,f250])).
% 0.22/0.56  fof(f250,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f249,f142])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f139,f124])).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f55,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    ( ! [X0] : (v1_xboole_0(k5_xboole_0(X0,X0))) )),
% 0.22/0.56    inference(resolution,[],[f138,f135])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k5_xboole_0(X0,X0),X0) | v1_xboole_0(k5_xboole_0(X0,X0))) )),
% 0.22/0.56    inference(resolution,[],[f134,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 0.22/0.56    inference(superposition,[],[f85,f84])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f44,f81])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.56    inference(rectify,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f45,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f50,f81])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 0.22/0.56    inference(superposition,[],[f86,f84])).
% 0.22/0.56  % (16438)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.57  fof(f86,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f46,f82])).
% 1.56/0.57  % (16450)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.56/0.57  fof(f249,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.56/0.57    inference(subsumption_resolution,[],[f248,f108])).
% 1.56/0.57  fof(f108,plain,(
% 1.56/0.57    ( ! [X6,X2,X0,X3,X1] : (r2_hidden(X6,k4_enumset1(X0,X0,X1,X2,X3,X6))) )),
% 1.56/0.57    inference(equality_resolution,[],[f107])).
% 1.56/0.57  fof(f107,plain,(
% 1.56/0.57    ( ! [X6,X2,X0,X5,X3,X1] : (r2_hidden(X6,X5) | k4_enumset1(X0,X0,X1,X2,X3,X6) != X5) )),
% 1.56/0.57    inference(equality_resolution,[],[f95])).
% 1.56/0.57  fof(f95,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 1.56/0.57    inference(definition_unfolding,[],[f77,f65])).
% 1.56/0.57  fof(f77,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.56/0.57    inference(cnf_transformation,[],[f36])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.56/0.57    inference(ennf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.56/0.57  fof(f248,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1)) | ~r2_hidden(X1,k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.56/0.57    inference(superposition,[],[f93,f84])).
% 1.56/0.57  fof(f93,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) | ~r2_hidden(X1,X2)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f62,f80,f82,f80])).
% 1.56/0.57  fof(f62,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.56/0.57  fof(f311,plain,(
% 1.56/0.57    k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 1.56/0.57    inference(duplicate_literal_removal,[],[f310])).
% 1.56/0.57  fof(f310,plain,(
% 1.56/0.57    k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.56/0.57    inference(resolution,[],[f230,f42])).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(flattening,[],[f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f21])).
% 1.56/0.57  fof(f21,axiom,(
% 1.56/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 1.56/0.57  fof(f230,plain,(
% 1.56/0.57    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.56/0.57    inference(subsumption_resolution,[],[f226,f108])).
% 1.56/0.57  fof(f226,plain,(
% 1.56/0.57    ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.56/0.57    inference(resolution,[],[f225,f210])).
% 1.56/0.57  fof(f210,plain,(
% 1.56/0.57    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.56/0.57    inference(subsumption_resolution,[],[f209,f40])).
% 1.56/0.57  fof(f209,plain,(
% 1.56/0.57    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.56/0.57    inference(subsumption_resolution,[],[f208,f37])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    v1_relat_1(sK2)),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f208,plain,(
% 1.56/0.57    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.56/0.57    inference(resolution,[],[f207,f42])).
% 1.56/0.57  fof(f207,plain,(
% 1.56/0.57    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.56/0.57    inference(resolution,[],[f83,f88])).
% 1.56/0.57  fof(f88,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f57,f81])).
% 1.56/0.57  fof(f57,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f35])).
% 1.56/0.57  fof(f35,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.57    inference(flattening,[],[f34])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(ennf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.56/0.57  fof(f83,plain,(
% 1.56/0.57    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.56/0.57    inference(definition_unfolding,[],[f38,f81,f81])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.56/0.57    inference(cnf_transformation,[],[f25])).
% 1.56/0.57  fof(f225,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.56/0.57    inference(duplicate_literal_removal,[],[f224])).
% 1.56/0.57  fof(f224,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 1.56/0.57    inference(superposition,[],[f166,f84])).
% 1.56/0.57  fof(f166,plain,(
% 1.56/0.57    ( ! [X6,X8,X7] : (r1_tarski(k1_setfam_1(X7),k1_setfam_1(k4_enumset1(X8,X8,X8,X8,X8,X6))) | ~r2_hidden(X8,X7) | k1_xboole_0 = k4_enumset1(X8,X8,X8,X8,X8,X6) | ~r2_hidden(X6,X7)) )),
% 1.56/0.57    inference(resolution,[],[f89,f52])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.56/0.57    inference(flattening,[],[f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f19])).
% 1.56/0.57  fof(f19,axiom,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.56/0.57  fof(f89,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f60,f80])).
% 1.56/0.57  fof(f60,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f14])).
% 1.56/0.57  fof(f14,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (16439)------------------------------
% 1.56/0.57  % (16439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (16439)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (16439)Memory used [KB]: 6524
% 1.56/0.57  % (16439)Time elapsed: 0.143 s
% 1.56/0.57  % (16439)------------------------------
% 1.56/0.57  % (16439)------------------------------
% 1.56/0.57  % (16450)Refutation not found, incomplete strategy% (16450)------------------------------
% 1.56/0.57  % (16450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (16444)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.57  % (16431)Success in time 0.201 s
%------------------------------------------------------------------------------
