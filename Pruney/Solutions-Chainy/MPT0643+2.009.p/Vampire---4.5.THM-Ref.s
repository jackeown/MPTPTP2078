%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 263 expanded)
%              Number of leaves         :    7 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 (1783 expanded)
%              Number of equality atoms :   92 ( 705 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(subsumption_resolution,[],[f271,f71])).

fof(f71,plain,(
    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f70,f29])).

fof(f29,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f70,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f69,f25])).

fof(f25,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f68,f25])).

fof(f68,plain,
    ( sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,
    ( ~ v1_relat_1(sK2)
    | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f23,f49])).

fof(f49,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f271,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f254,f126])).

fof(f126,plain,(
    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) ),
    inference(resolution,[],[f99,f67])).

fof(f67,plain,(
    r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,
    ( sK2 = k6_relat_1(sK0)
    | r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f65,f25])).

fof(f65,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f64,f25])).

fof(f64,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f56,f22])).

fof(f56,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f23,f50])).

fof(f50,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(forward_demodulation,[],[f98,f24])).

fof(f24,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f97,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f95,f22])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f94,f31])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(superposition,[],[f40,f28])).

fof(f28,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f254,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(resolution,[],[f132,f136])).

fof(f136,plain,(
    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) ),
    inference(resolution,[],[f131,f67])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),sK0) ) ),
    inference(forward_demodulation,[],[f130,f25])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),sK0) ) ),
    inference(superposition,[],[f110,f93])).

fof(f93,plain,(
    sK2 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f92,f22])).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f26,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f26,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X2,sK2)))
      | r2_hidden(k1_funct_1(sK2,X3),X2) ) ),
    inference(subsumption_resolution,[],[f109,f22])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X2,sK2)))
      | r2_hidden(k1_funct_1(sK2,X3),X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f104,f23])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X2,sK2)))
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X3),X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f33,f51])).

fof(f51,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(resolution,[],[f22,f39])).

% (5945)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | sK3(sK0,sK2) = X0 ) ),
    inference(resolution,[],[f88,f67])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f87,f27])).

fof(f27,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f86,f30])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f41,f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:20:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (5928)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (5927)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (5925)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (5933)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (5922)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (5930)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (5925)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (5920)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (5942)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (5927)Refutation not found, incomplete strategy% (5927)------------------------------
% 0.21/0.50  % (5927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5927)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5927)Memory used [KB]: 1663
% 0.21/0.50  % (5927)Time elapsed: 0.095 s
% 0.21/0.50  % (5927)------------------------------
% 0.21/0.50  % (5927)------------------------------
% 0.21/0.50  % (5924)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (5943)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (5929)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (5941)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (5934)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (5935)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (5921)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (5937)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (5939)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (5923)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f271,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    sK2 != k6_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    sK2 = k6_relat_1(sK0) | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f69,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f68,f25])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f57,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f23,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f254,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))),
% 0.21/0.51    inference(resolution,[],[f99,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f29])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    sK2 = k6_relat_1(sK0) | r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f65,f25])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    r2_hidden(sK3(sK0,sK2),sK0) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f64,f25])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f22])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f23,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f98,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f23])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f22])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.51    inference(superposition,[],[f40,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.51    inference(resolution,[],[f132,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)),
% 0.21/0.51    inference(resolution,[],[f131,f67])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),sK0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f130,f25])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),sK0)) )),
% 0.21/0.51    inference(superposition,[],[f110,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    sK2 = k8_relat_1(sK0,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f22])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | sK2 = k8_relat_1(sK0,sK2)),
% 0.21/0.51    inference(resolution,[],[f26,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k8_relat_1(X2,sK2))) | r2_hidden(k1_funct_1(sK2,X3),X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f22])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k8_relat_1(X2,sK2))) | r2_hidden(k1_funct_1(sK2,X3),X2) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f23])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k8_relat_1(X2,sK2))) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X3),X2) | ~v1_relat_1(sK2)) )),
% 0.21/0.51    inference(superposition,[],[f33,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f22,f39])).
% 0.21/0.51  % (5945)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | sK3(sK0,sK2) = X0) )),
% 0.21/0.51    inference(resolution,[],[f88,f67])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f30])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f31])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.51    inference(superposition,[],[f41,f24])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5925)------------------------------
% 0.21/0.51  % (5925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5925)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5925)Memory used [KB]: 6268
% 0.21/0.51  % (5925)Time elapsed: 0.092 s
% 0.21/0.51  % (5925)------------------------------
% 0.21/0.51  % (5925)------------------------------
% 0.21/0.51  % (5926)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (5919)Success in time 0.157 s
%------------------------------------------------------------------------------
