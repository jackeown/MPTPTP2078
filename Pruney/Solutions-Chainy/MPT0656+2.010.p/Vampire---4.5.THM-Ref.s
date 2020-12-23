%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 (1030 expanded)
%              Number of leaves         :   11 ( 187 expanded)
%              Depth                    :   22
%              Number of atoms          :  268 (5385 expanded)
%              Number of equality atoms :  112 (1962 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f894,plain,(
    $false ),
    inference(subsumption_resolution,[],[f893,f108])).

fof(f108,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f32,f81])).

fof(f81,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f34,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f80,plain,
    ( ~ v1_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f74,f33])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f29,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f893,plain,(
    sK1 = k4_relat_1(sK0) ),
    inference(forward_demodulation,[],[f868,f884])).

fof(f884,plain,(
    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f477,f878])).

fof(f878,plain,(
    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f189,f867])).

fof(f867,plain,(
    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),sK1) ),
    inference(backward_demodulation,[],[f350,f864])).

fof(f864,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f82,f863])).

fof(f863,plain,(
    k5_relat_1(k4_relat_1(sK0),sK0) = k5_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f861,f772])).

fof(f772,plain,(
    sK1 = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f771,f350])).

fof(f771,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f769,f82])).

fof(f769,plain,(
    k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),sK1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f682,f33])).

fof(f682,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(k4_relat_1(X5),sK0),sK1) = k5_relat_1(k4_relat_1(X5),k5_relat_1(sK0,sK1)) ) ),
    inference(resolution,[],[f237,f33])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(k4_relat_1(X1),X0),sK1) = k5_relat_1(k4_relat_1(X1),k5_relat_1(X0,sK1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f55,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),sK1) = k5_relat_1(X4,k5_relat_1(X5,sK1)) ) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f861,plain,(
    k5_relat_1(k4_relat_1(sK0),sK0) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)),sK0) ),
    inference(resolution,[],[f857,f33])).

fof(f857,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k4_relat_1(X2),sK0) = k5_relat_1(k5_relat_1(k4_relat_1(X2),k5_relat_1(sK0,sK1)),sK0) ) ),
    inference(forward_demodulation,[],[f853,f576])).

fof(f576,plain,(
    sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f211,f575])).

fof(f575,plain,(
    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f574,f85])).

fof(f85,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f574,plain,(
    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f573,f211])).

fof(f573,plain,(
    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(k5_relat_1(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f572,f83])).

fof(f83,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f77,f81])).

fof(f77,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f76,f31])).

fof(f31,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f75,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f72,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f572,plain,(
    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0) ),
    inference(forward_demodulation,[],[f570,f82])).

fof(f570,plain,(
    k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0) = k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(resolution,[],[f300,f33])).

fof(f300,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(sK0,k4_relat_1(X0)),sK0) = k5_relat_1(sK0,k5_relat_1(k4_relat_1(X0),sK0)) ) ),
    inference(resolution,[],[f298,f39])).

fof(f298,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(sK0,X5),sK0) = k5_relat_1(sK0,k5_relat_1(X5,sK0)) ) ),
    inference(resolution,[],[f90,f33])).

fof(f90,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),sK0) = k5_relat_1(X4,k5_relat_1(X5,sK0)) ) ),
    inference(resolution,[],[f33,f43])).

fof(f211,plain,(
    k5_relat_1(k5_relat_1(sK0,sK1),sK0) = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f206,f33])).

fof(f206,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(sK0,sK1),X5) = k5_relat_1(sK0,k5_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK1),X3) = k5_relat_1(X2,k5_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f27,f43])).

fof(f853,plain,(
    ! [X2] :
      ( k5_relat_1(k5_relat_1(k4_relat_1(X2),k5_relat_1(sK0,sK1)),sK0) = k5_relat_1(k4_relat_1(X2),k5_relat_1(k5_relat_1(sK0,sK1),sK0))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f295,f114])).

fof(f114,plain,(
    v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(k4_relat_1(X1),X0),sK0) = k5_relat_1(k4_relat_1(X1),k5_relat_1(X0,sK0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f90,f39])).

fof(f82,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    inference(backward_demodulation,[],[f79,f81])).

fof(f79,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f73,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(resolution,[],[f29,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f350,plain,(
    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(resolution,[],[f347,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | sK1 = k5_relat_1(k6_relat_1(X0),sK1) ) ),
    inference(subsumption_resolution,[],[f105,f27])).

% (26623)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f105,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ v1_relat_1(sK1)
      | sK1 = k5_relat_1(k6_relat_1(X0),sK1) ) ),
    inference(superposition,[],[f48,f30])).

fof(f30,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f347,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f346,f112])).

fof(f112,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f37,f31])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f346,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f337,f33])).

fof(f337,plain,
    ( ~ v1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f71,f34])).

fof(f71,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),k2_relat_1(sK0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,sK1)) ) ),
    inference(forward_demodulation,[],[f70,f30])).

fof(f70,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,sK1))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f64,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,sK1))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f189,plain,(
    k5_relat_1(sK1,k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK1,sK0),sK1) ),
    inference(resolution,[],[f179,f27])).

fof(f179,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(sK1,sK0),X5) = k5_relat_1(sK1,k5_relat_1(sK0,X5)) ) ),
    inference(resolution,[],[f53,f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f27,f43])).

fof(f477,plain,(
    k5_relat_1(sK1,k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f475,f83])).

fof(f475,plain,(
    k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f185,f33])).

fof(f185,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(X0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(X0))) ) ),
    inference(resolution,[],[f179,f39])).

fof(f868,plain,(
    k4_relat_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f406,f864])).

fof(f406,plain,(
    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f405,f33])).

fof(f405,plain,
    ( k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f388,f39])).

fof(f388,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(resolution,[],[f149,f347])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ v1_relat_1(k4_relat_1(sK0))
      | k4_relat_1(sK0) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK0)) ) ),
    inference(superposition,[],[f48,f86])).

fof(f86,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (26631)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.45  % (26625)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (26633)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (26639)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (26627)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (26635)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (26633)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f894,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f893,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    sK1 != k4_relat_1(sK0)),
% 0.21/0.51    inference(superposition,[],[f32,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f29,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK1 != k2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f893,plain,(
% 0.21/0.51    sK1 = k4_relat_1(sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f868,f884])).
% 0.21/0.51  fof(f884,plain,(
% 0.21/0.51    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f477,f878])).
% 0.21/0.51  fof(f878,plain,(
% 0.21/0.51    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(backward_demodulation,[],[f189,f867])).
% 0.21/0.51  fof(f867,plain,(
% 0.21/0.51    sK1 = k5_relat_1(k5_relat_1(sK1,sK0),sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f350,f864])).
% 0.21/0.51  fof(f864,plain,(
% 0.21/0.51    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f82,f863])).
% 0.21/0.51  fof(f863,plain,(
% 0.21/0.51    k5_relat_1(k4_relat_1(sK0),sK0) = k5_relat_1(sK1,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f861,f772])).
% 0.21/0.51  fof(f772,plain,(
% 0.21/0.51    sK1 = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f771,f350])).
% 0.21/0.51  fof(f771,plain,(
% 0.21/0.51    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f769,f82])).
% 0.21/0.51  fof(f769,plain,(
% 0.21/0.51    k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),sK1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f682,f33])).
% 0.21/0.51  fof(f682,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(k4_relat_1(X5),sK0),sK1) = k5_relat_1(k4_relat_1(X5),k5_relat_1(sK0,sK1))) )),
% 0.21/0.51    inference(resolution,[],[f237,f33])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(k4_relat_1(X1),X0),sK1) = k5_relat_1(k4_relat_1(X1),k5_relat_1(X0,sK1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f55,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),sK1) = k5_relat_1(X4,k5_relat_1(X5,sK1))) )),
% 0.21/0.51    inference(resolution,[],[f27,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f861,plain,(
% 0.21/0.51    k5_relat_1(k4_relat_1(sK0),sK0) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)),sK0)),
% 0.21/0.51    inference(resolution,[],[f857,f33])).
% 0.21/0.51  fof(f857,plain,(
% 0.21/0.51    ( ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k4_relat_1(X2),sK0) = k5_relat_1(k5_relat_1(k4_relat_1(X2),k5_relat_1(sK0,sK1)),sK0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f853,f576])).
% 0.21/0.51  fof(f576,plain,(
% 0.21/0.51    sK0 = k5_relat_1(k5_relat_1(sK0,sK1),sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f211,f575])).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f574,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.51    inference(resolution,[],[f33,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f573,f211])).
% 0.21/0.51  fof(f573,plain,(
% 0.21/0.51    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(k5_relat_1(sK0,sK1),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f572,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f77,f81])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f76,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f34])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f33])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f29,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.51  fof(f572,plain,(
% 0.21/0.51    k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f570,f82])).
% 0.21/0.51  fof(f570,plain,(
% 0.21/0.51    k5_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)),sK0) = k5_relat_1(sK0,k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.51    inference(resolution,[],[f300,f33])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(sK0,k4_relat_1(X0)),sK0) = k5_relat_1(sK0,k5_relat_1(k4_relat_1(X0),sK0))) )),
% 0.21/0.51    inference(resolution,[],[f298,f39])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(sK0,X5),sK0) = k5_relat_1(sK0,k5_relat_1(X5,sK0))) )),
% 0.21/0.51    inference(resolution,[],[f90,f33])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),sK0) = k5_relat_1(X4,k5_relat_1(X5,sK0))) )),
% 0.21/0.51    inference(resolution,[],[f33,f43])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    k5_relat_1(k5_relat_1(sK0,sK1),sK0) = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.21/0.51    inference(resolution,[],[f206,f33])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(sK0,sK1),X5) = k5_relat_1(sK0,k5_relat_1(sK1,X5))) )),
% 0.21/0.51    inference(resolution,[],[f54,f33])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK1),X3) = k5_relat_1(X2,k5_relat_1(sK1,X3))) )),
% 0.21/0.51    inference(resolution,[],[f27,f43])).
% 0.21/0.51  fof(f853,plain,(
% 0.21/0.51    ( ! [X2] : (k5_relat_1(k5_relat_1(k4_relat_1(X2),k5_relat_1(sK0,sK1)),sK0) = k5_relat_1(k4_relat_1(X2),k5_relat_1(k5_relat_1(sK0,sK1),sK0)) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(resolution,[],[f295,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f35,f31])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(k4_relat_1(X1),X0),sK0) = k5_relat_1(k4_relat_1(X1),k5_relat_1(X0,sK0)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f90,f39])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f79,f81])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f34])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f33])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.21/0.51    inference(resolution,[],[f29,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    sK1 = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1)),
% 0.21/0.51    inference(resolution,[],[f347,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK1 = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f105,f27])).
% 0.21/0.51  % (26623)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | ~v1_relat_1(sK1) | sK1 = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.21/0.51    inference(superposition,[],[f48,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f346,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f37,f31])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f337,f33])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f71,f34])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),k2_relat_1(sK0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,sK1))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f70,f30])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,sK1)) | r1_tarski(k2_relat_1(X1),k1_relat_1(sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f64,f27])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_relat_1(sK1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,sK1)) | r1_tarski(k2_relat_1(X1),k1_relat_1(sK1))) )),
% 0.21/0.51    inference(resolution,[],[f28,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    k5_relat_1(sK1,k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK1,sK0),sK1)),
% 0.21/0.51    inference(resolution,[],[f179,f27])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(sK1,sK0),X5) = k5_relat_1(sK1,k5_relat_1(sK0,X5))) )),
% 0.21/0.52    inference(resolution,[],[f53,f33])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1))) )),
% 0.21/0.52    inference(resolution,[],[f27,f43])).
% 0.21/0.52  fof(f477,plain,(
% 0.21/0.52    k5_relat_1(sK1,k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f475,f83])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.52    inference(resolution,[],[f185,f33])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(X0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(X0)))) )),
% 0.21/0.52    inference(resolution,[],[f179,f39])).
% 0.21/0.52  fof(f868,plain,(
% 0.21/0.52    k4_relat_1(sK0) = k5_relat_1(k5_relat_1(sK1,sK0),k4_relat_1(sK0))),
% 0.21/0.52    inference(backward_demodulation,[],[f406,f864])).
% 0.21/0.52  fof(f406,plain,(
% 0.21/0.52    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f405,f33])).
% 0.21/0.52  fof(f405,plain,(
% 0.21/0.52    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f388,f39])).
% 0.21/0.52  fof(f388,plain,(
% 0.21/0.52    ~v1_relat_1(k4_relat_1(sK0)) | k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f149,f347])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | ~v1_relat_1(k4_relat_1(sK0)) | k4_relat_1(sK0) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK0))) )),
% 0.21/0.52    inference(superposition,[],[f48,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f33,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (26633)------------------------------
% 0.21/0.52  % (26633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26633)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (26633)Memory used [KB]: 2302
% 0.21/0.52  % (26633)Time elapsed: 0.053 s
% 0.21/0.52  % (26633)------------------------------
% 0.21/0.52  % (26633)------------------------------
% 0.21/0.52  % (26621)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (26634)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (26632)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (26632)Refutation not found, incomplete strategy% (26632)------------------------------
% 0.21/0.52  % (26632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26632)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26632)Memory used [KB]: 6012
% 0.21/0.52  % (26632)Time elapsed: 0.001 s
% 0.21/0.52  % (26632)------------------------------
% 0.21/0.52  % (26632)------------------------------
% 0.21/0.52  % (26617)Success in time 0.154 s
%------------------------------------------------------------------------------
