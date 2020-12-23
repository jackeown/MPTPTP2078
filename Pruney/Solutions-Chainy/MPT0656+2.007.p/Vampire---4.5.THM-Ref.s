%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 439 expanded)
%              Number of leaves         :   12 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 (2303 expanded)
%              Number of equality atoms :   94 ( 837 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (15982)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f919,plain,(
    $false ),
    inference(subsumption_resolution,[],[f918,f185])).

fof(f185,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f34,f86])).

fof(f86,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f36,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k1_relat_1(X1) = k2_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f85,plain,
    ( ~ v1_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f918,plain,(
    sK1 = k4_relat_1(sK0) ),
    inference(backward_demodulation,[],[f553,f917])).

fof(f917,plain,(
    sK1 = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f914,f603])).

fof(f603,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f602,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f602,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f600,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f600,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f599,f32])).

fof(f32,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f599,plain,(
    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f598,f149])).

fof(f149,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f40,f33])).

fof(f33,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f598,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f587,f35])).

fof(f587,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f74,f36])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1))
      | r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f71,f29])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1))
      | r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f30,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f914,plain,(
    k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f499,f29])).

fof(f499,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f490,f87])).

fof(f87,plain,(
    k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    inference(backward_demodulation,[],[f84,f86])).

fof(f84,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f83,f32])).

fof(f83,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f82,f36])).

fof(f82,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f77,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f490,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f93,f112])).

fof(f112,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f111,f86])).

fof(f111,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f104,f35])).

fof(f104,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f93,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,sK0),X5) = k5_relat_1(X4,k5_relat_1(sK0,X5)) ) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f553,plain,(
    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f442,f550])).

fof(f550,plain,(
    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f549,f103])).

fof(f103,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f89,f32])).

fof(f89,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f549,plain,(
    k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f548,f438])).

fof(f438,plain,(
    k5_relat_1(k5_relat_1(sK0,sK1),sK0) = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f376,f35])).

fof(f376,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(sK0,sK1),X9) = k5_relat_1(sK0,k5_relat_1(sK1,X9)) ) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,sK1),X5) = k5_relat_1(X4,k5_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f29,f44])).

fof(f548,plain,(
    k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f547,f88])).

fof(f88,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f81,f86])).

fof(f81,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f80,f33])).

fof(f80,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f79,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f547,plain,(
    k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0) ),
    inference(forward_demodulation,[],[f538,f87])).

fof(f538,plain,(
    k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0) = k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(resolution,[],[f535,f112])).

fof(f535,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(sK0,X9),sK0) = k5_relat_1(sK0,k5_relat_1(X9,sK0)) ) ),
    inference(resolution,[],[f94,f35])).

fof(f94,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(X6,X7),sK0) = k5_relat_1(X6,k5_relat_1(X7,sK0)) ) ),
    inference(resolution,[],[f35,f44])).

fof(f442,plain,(
    k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f335,f438])).

fof(f335,plain,(
    k4_relat_1(k5_relat_1(k5_relat_1(sK0,sK1),sK0)) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f326,f153])).

fof(f153,plain,(
    k5_relat_1(sK0,sK1) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f37,f33])).

fof(f37,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f326,plain,(
    k4_relat_1(k5_relat_1(k5_relat_1(sK0,sK1),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f91,f151])).

fof(f151,plain,(
    v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f38,f33])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f91,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X1,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X1)) ) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (15973)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.44  % (15978)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.45  % (15988)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (15988)Refutation not found, incomplete strategy% (15988)------------------------------
% 0.20/0.45  % (15988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (15988)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (15988)Memory used [KB]: 10618
% 0.20/0.45  % (15988)Time elapsed: 0.065 s
% 0.20/0.45  % (15988)------------------------------
% 0.20/0.45  % (15988)------------------------------
% 0.20/0.45  % (15970)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.45  % (15985)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % (15981)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (15984)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (15971)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (15981)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (15982)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  fof(f919,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f918,f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    sK1 != k4_relat_1(sK0)),
% 0.20/0.49    inference(superposition,[],[f34,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f85,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v1_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ~v1_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.49    inference(resolution,[],[f31,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v2_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    sK1 != k2_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f918,plain,(
% 0.20/0.49    sK1 = k4_relat_1(sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f553,f917])).
% 0.20/0.49  fof(f917,plain,(
% 0.20/0.49    sK1 = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f914,f603])).
% 0.20/0.49  fof(f603,plain,(
% 0.20/0.49    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f602,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v1_relat_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f602,plain,(
% 0.20/0.49    ~v1_relat_1(sK1) | sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.49    inference(resolution,[],[f600,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.49  fof(f600,plain,(
% 0.20/0.49    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f599,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f599,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f598,f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.49    inference(superposition,[],[f40,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f598,plain,(
% 0.20/0.49    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f587,f35])).
% 0.20/0.49  fof(f587,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.49    inference(resolution,[],[f74,f36])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1)) | r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f71,f29])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK1)) | r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f30,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f914,plain,(
% 0.20/0.49    k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.49    inference(resolution,[],[f499,f29])).
% 0.20/0.49  fof(f499,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f490,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f84,f86])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f83,f32])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f82,f36])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f35])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.49    inference(resolution,[],[f31,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.49  fof(f490,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X1))) )),
% 0.20/0.49    inference(resolution,[],[f93,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.49    inference(forward_demodulation,[],[f111,f86])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f104,f35])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.49    inference(resolution,[],[f36,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,sK0),X5) = k5_relat_1(X4,k5_relat_1(sK0,X5))) )),
% 0.20/0.49    inference(resolution,[],[f35,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.49  fof(f553,plain,(
% 0.20/0.49    k4_relat_1(sK0) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.20/0.49    inference(backward_demodulation,[],[f442,f550])).
% 0.20/0.49  fof(f550,plain,(
% 0.20/0.49    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.20/0.49    inference(forward_demodulation,[],[f549,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    sK0 = k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1)))),
% 0.20/0.49    inference(forward_demodulation,[],[f89,f32])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.20/0.49    inference(resolution,[],[f35,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.49  fof(f549,plain,(
% 0.20/0.49    k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.20/0.49    inference(forward_demodulation,[],[f548,f438])).
% 0.20/0.49  fof(f438,plain,(
% 0.20/0.49    k5_relat_1(k5_relat_1(sK0,sK1),sK0) = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.20/0.49    inference(resolution,[],[f376,f35])).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(sK0,sK1),X9) = k5_relat_1(sK0,k5_relat_1(sK1,X9))) )),
% 0.20/0.49    inference(resolution,[],[f56,f35])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,sK1),X5) = k5_relat_1(X4,k5_relat_1(sK1,X5))) )),
% 0.20/0.49    inference(resolution,[],[f29,f44])).
% 0.20/0.49  fof(f548,plain,(
% 0.20/0.49    k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK0,sK1),sK0)),
% 0.20/0.49    inference(forward_demodulation,[],[f547,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.20/0.49    inference(backward_demodulation,[],[f81,f86])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.49    inference(forward_demodulation,[],[f80,f33])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f79,f36])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f35])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.20/0.49    inference(resolution,[],[f31,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f547,plain,(
% 0.20/0.49    k5_relat_1(sK0,k6_relat_1(k1_relat_1(sK1))) = k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0)),
% 0.20/0.49    inference(forward_demodulation,[],[f538,f87])).
% 0.20/0.49  fof(f538,plain,(
% 0.20/0.49    k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0) = k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.20/0.49    inference(resolution,[],[f535,f112])).
% 0.20/0.49  fof(f535,plain,(
% 0.20/0.49    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(sK0,X9),sK0) = k5_relat_1(sK0,k5_relat_1(X9,sK0))) )),
% 0.20/0.49    inference(resolution,[],[f94,f35])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X6,X7] : (~v1_relat_1(X6) | ~v1_relat_1(X7) | k5_relat_1(k5_relat_1(X6,X7),sK0) = k5_relat_1(X6,k5_relat_1(X7,sK0))) )),
% 0.20/0.49    inference(resolution,[],[f35,f44])).
% 0.20/0.49  fof(f442,plain,(
% 0.20/0.49    k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,k5_relat_1(sK1,sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f335,f438])).
% 0.20/0.49  fof(f335,plain,(
% 0.20/0.49    k4_relat_1(k5_relat_1(k5_relat_1(sK0,sK1),sK0)) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f326,f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    k5_relat_1(sK0,sK1) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.49    inference(superposition,[],[f37,f33])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.49  fof(f326,plain,(
% 0.20/0.49    k4_relat_1(k5_relat_1(k5_relat_1(sK0,sK1),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.49    inference(resolution,[],[f91,f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.49    inference(superposition,[],[f38,f33])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X1))) )),
% 0.20/0.49    inference(resolution,[],[f35,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (15981)------------------------------
% 0.20/0.49  % (15981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15981)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (15981)Memory used [KB]: 2174
% 0.20/0.49  % (15981)Time elapsed: 0.102 s
% 0.20/0.49  % (15981)------------------------------
% 0.20/0.49  % (15981)------------------------------
% 0.20/0.49  % (15967)Success in time 0.137 s
%------------------------------------------------------------------------------
