%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 233 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  236 ( 883 expanded)
%              Number of equality atoms :   52 ( 162 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(subsumption_resolution,[],[f427,f448])).

fof(f448,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f68,f447])).

fof(f447,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f446,f245])).

fof(f245,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f181,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f181,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f180,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f180,plain,(
    ! [X1] : r1_tarski(k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)),X1) ),
    inference(subsumption_resolution,[],[f173,f134])).

fof(f134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f69,f71])).

fof(f71,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK1) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X0)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X0)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X1) = k1_relat_1(X0)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X0)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(resolution,[],[f57,f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f173,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)),X1) ) ),
    inference(resolution,[],[f133,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f133,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f75,f71])).

fof(f75,plain,(
    ! [X0] : v1_funct_1(k8_relat_1(X0,sK1)) ),
    inference(subsumption_resolution,[],[f73,f38])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | v1_funct_1(k8_relat_1(X0,sK1)) ) ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f446,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(resolution,[],[f421,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f421,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f420])).

fof(f420,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f65,f206])).

fof(f206,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f205,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f205,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f204,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f204,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f201,f45])).

fof(f201,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f134,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f19])).

% (31667)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f68,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f427,plain,(
    k1_xboole_0 = k1_tarski(k1_funct_1(sK0,sK2(sK1))) ),
    inference(forward_demodulation,[],[f426,f206])).

fof(f426,plain,(
    k1_tarski(k1_funct_1(sK0,sK2(sK1))) = k3_xboole_0(k1_xboole_0,k1_tarski(k1_funct_1(sK0,sK2(sK1)))) ),
    inference(resolution,[],[f380,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f380,plain,(
    r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f379,f148])).

fof(f148,plain,(
    k1_xboole_0 = k1_funct_1(sK1,sK2(sK1)) ),
    inference(resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f88,plain,(
    v1_xboole_0(k1_funct_1(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f87,f42])).

fof(f42,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,
    ( v1_xboole_0(k1_funct_1(sK1,sK2(sK1)))
    | v2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(k1_funct_1(sK1,sK2(sK1)))
    | v2_relat_1(sK1) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | v2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

fof(f379,plain,(
    r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f378,f39])).

fof(f378,plain,
    ( r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f377,f38])).

fof(f377,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f145,f40])).

fof(f40,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v5_funct_1(sK0,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(X0,sK2(sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f44,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(X0,sK2(sK1)))
      | ~ v5_funct_1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f141,f43])).

% (31660)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(X0,sK2(sK1)))
      | ~ v5_funct_1(sK0,X0) ) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
      | ~ v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f83,plain,(
    r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f82,f41])).

fof(f41,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    r2_hidden(sK2(sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | v2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f79,f38])).

fof(f79,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | v2_relat_1(sK1) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (31673)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (31673)Refutation not found, incomplete strategy% (31673)------------------------------
% 0.21/0.44  % (31673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (31673)Memory used [KB]: 10618
% 0.21/0.44  % (31673)Time elapsed: 0.028 s
% 0.21/0.44  % (31673)------------------------------
% 0.21/0.44  % (31673)------------------------------
% 0.21/0.47  % (31665)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (31670)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (31654)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31655)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (31654)Refutation not found, incomplete strategy% (31654)------------------------------
% 0.21/0.48  % (31654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31654)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31654)Memory used [KB]: 10618
% 0.21/0.48  % (31654)Time elapsed: 0.059 s
% 0.21/0.48  % (31654)------------------------------
% 0.21/0.48  % (31654)------------------------------
% 0.21/0.48  % (31670)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f450,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f427,f448])).
% 0.21/0.48  fof(f448,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f68,f447])).
% 0.21/0.48  fof(f447,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f446,f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.48    inference(resolution,[],[f181,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f180,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)),X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f173,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    v1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(superposition,[],[f69,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK1)),
% 0.21/0.48    inference(resolution,[],[f50,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X0) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X1) = k1_relat_1(X0) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X1) = k1_relat_1(X0) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f17])).
% 0.21/0.48  fof(f17,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X1) = k1_relat_1(X0) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f57,f38])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X1)),X1)) )),
% 0.21/0.48    inference(resolution,[],[f133,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    v1_funct_1(k1_xboole_0)),
% 0.21/0.48    inference(superposition,[],[f75,f71])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k8_relat_1(X0,sK1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f38])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK1) | v1_funct_1(k8_relat_1(X0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f64,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_1(k8_relat_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).
% 0.21/0.48  fof(f446,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f421,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f420])).
% 0.21/0.48  fof(f420,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(superposition,[],[f65,f206])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f205,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f204,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f201,f45])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f134,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  % (31667)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tarski(k1_funct_1(sK0,sK2(sK1)))),
% 0.21/0.48    inference(forward_demodulation,[],[f426,f206])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    k1_tarski(k1_funct_1(sK0,sK2(sK1))) = k3_xboole_0(k1_xboole_0,k1_tarski(k1_funct_1(sK0,sK2(sK1))))),
% 0.21/0.48    inference(resolution,[],[f380,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_xboole_0)),
% 0.21/0.48    inference(forward_demodulation,[],[f379,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    k1_xboole_0 = k1_funct_1(sK1,sK2(sK1))),
% 0.21/0.48    inference(resolution,[],[f88,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v1_xboole_0(k1_funct_1(sK1,sK2(sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v2_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v1_xboole_0(k1_funct_1(sK1,sK2(sK1))) | v2_relat_1(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f38])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | v1_xboole_0(k1_funct_1(sK1,sK2(sK1))) | v2_relat_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f53,f39])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_xboole_0(k1_funct_1(X0,sK2(X0))) | v2_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f378,f39])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1))) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f377,f38])).
% 0.21/0.48  fof(f377,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1))) | ~v1_funct_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f145,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v5_funct_1(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_funct_1(sK0,X0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(X0,sK2(sK1))) | ~v1_funct_1(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f144,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_1(sK0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(X0,sK2(sK1))) | ~v5_funct_1(sK0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f43])).
% 0.21/0.48  % (31660)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(X0,sK2(sK1))) | ~v5_funct_1(sK0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f83,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~v5_funct_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    r2_hidden(sK2(sK1),k1_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f82,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    k1_relat_1(sK1) = k1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    r2_hidden(sK2(sK1),k1_relat_1(sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f42])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r2_hidden(sK2(sK1),k1_relat_1(sK1)) | v2_relat_1(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f38])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | r2_hidden(sK2(sK1),k1_relat_1(sK1)) | v2_relat_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f52,f39])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | v2_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31670)------------------------------
% 0.21/0.48  % (31670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31670)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31670)Memory used [KB]: 2046
% 0.21/0.48  % (31670)Time elapsed: 0.067 s
% 0.21/0.48  % (31670)------------------------------
% 0.21/0.48  % (31670)------------------------------
% 0.21/0.49  % (31652)Success in time 0.127 s
%------------------------------------------------------------------------------
