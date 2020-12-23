%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 554 expanded)
%              Number of leaves         :   11 (  98 expanded)
%              Depth                    :   23
%              Number of atoms          :  267 (2387 expanded)
%              Number of equality atoms :   92 ( 756 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f818,plain,(
    $false ),
    inference(subsumption_resolution,[],[f817,f603])).

fof(f603,plain,(
    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(subsumption_resolution,[],[f591,f131])).

fof(f131,plain,(
    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f130,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

% (15246)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f130,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f126,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f126,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(resolution,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f32,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f591,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(backward_demodulation,[],[f102,f590])).

fof(f590,plain,(
    k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0) ),
    inference(forward_demodulation,[],[f579,f131])).

fof(f579,plain,(
    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(resolution,[],[f359,f32])).

fof(f359,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK1))
      | sK3(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f358,f30])).

fof(f358,plain,(
    ! [X2] :
      ( sK3(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X2)))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f356,f29])).

fof(f356,plain,(
    ! [X2] :
      ( sK3(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X2)))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f99,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f93,f97])).

fof(f97,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f96,f30])).

fof(f96,plain,
    ( ~ v1_funct_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f91,f29])).

fof(f91,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f31,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f92,f30])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f102,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(backward_demodulation,[],[f28,f97])).

fof(f28,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f817,plain,(
    sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(forward_demodulation,[],[f816,f131])).

fof(f816,plain,(
    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(forward_demodulation,[],[f805,f590])).

fof(f805,plain,(
    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f402,f32])).

fof(f402,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f401,f137])).

fof(f137,plain,(
    v1_funct_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f136,f30])).

fof(f136,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f135,f29])).

fof(f135,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f42,f97])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f401,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(k4_relat_1(sK1))
      | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f400,f100])).

fof(f100,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f88,f97])).

fof(f88,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f75,f29])).

fof(f75,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f400,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(k4_relat_1(sK1))
      | ~ v1_funct_1(k4_relat_1(sK1))
      | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f399,f30])).

fof(f399,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(k4_relat_1(sK1))
      | ~ v1_funct_1(k4_relat_1(sK1))
      | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f391,f29])).

fof(f391,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(k4_relat_1(sK1))
      | ~ v1_funct_1(k4_relat_1(sK1))
      | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) ) ),
    inference(superposition,[],[f52,f386])).

fof(f386,plain,(
    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) ),
    inference(backward_demodulation,[],[f307,f385])).

fof(f385,plain,(
    k2_relat_1(sK1) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f376,f58])).

fof(f58,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f376,plain,(
    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f374,f121])).

fof(f121,plain,(
    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f103,f59])).

fof(f59,plain,(
    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k2_relat_1(k4_relat_1(sK1)))) ),
    inference(resolution,[],[f100,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f374,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0) ),
    inference(forward_demodulation,[],[f369,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f369,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f106,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f100,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (15241)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f307,plain,(
    k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f61,f100])).

fof(f61,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,sK1)) = k10_relat_1(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f29,f40])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (15237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (15244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (15236)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (15239)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (15245)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (15231)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15247)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (15233)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (15244)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (15251)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f818,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f817,f603])).
% 0.22/0.52  fof(f603,plain,(
% 0.22/0.52    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f591,f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.22/0.52  % (15246)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~v1_funct_1(sK1) | sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f126,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.52    inference(resolution,[],[f32,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f591,plain,(
% 0.22/0.52    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f102,f590])).
% 0.22/0.52  fof(f590,plain,(
% 0.22/0.52    k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f579,f131])).
% 1.25/0.52  fof(f579,plain,(
% 1.25/0.52    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 1.25/0.52    inference(resolution,[],[f359,f32])).
% 1.25/0.52  fof(f359,plain,(
% 1.25/0.52    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | sK3(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X2)))) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f358,f30])).
% 1.25/0.52  fof(f358,plain,(
% 1.25/0.52    ( ! [X2] : (sK3(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X2))) | ~v1_funct_1(sK1) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f356,f29])).
% 1.25/0.52  fof(f356,plain,(
% 1.25/0.52    ( ! [X2] : (sK3(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK3(sK1,X2))) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.25/0.52    inference(resolution,[],[f99,f56])).
% 1.25/0.52  fof(f56,plain,(
% 1.25/0.52    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.25/0.52    inference(equality_resolution,[],[f47])).
% 1.25/0.52  fof(f47,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f23])).
% 1.25/0.52  fof(f99,plain,(
% 1.25/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.25/0.52    inference(backward_demodulation,[],[f93,f97])).
% 1.25/0.52  fof(f97,plain,(
% 1.25/0.52    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.25/0.52    inference(subsumption_resolution,[],[f96,f30])).
% 1.25/0.52  fof(f96,plain,(
% 1.25/0.52    ~v1_funct_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.25/0.52    inference(subsumption_resolution,[],[f91,f29])).
% 1.25/0.52  fof(f91,plain,(
% 1.25/0.52    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.25/0.52    inference(resolution,[],[f31,f43])).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    v2_funct_1(sK1)),
% 1.25/0.52    inference(cnf_transformation,[],[f14])).
% 1.25/0.52  fof(f93,plain,(
% 1.25/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f92,f30])).
% 1.25/0.52  fof(f92,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f89,f29])).
% 1.25/0.52  fof(f89,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.25/0.52    inference(resolution,[],[f31,f50])).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f10])).
% 1.25/0.52  fof(f10,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 1.25/0.52  fof(f102,plain,(
% 1.25/0.52    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 1.25/0.52    inference(forward_demodulation,[],[f101,f97])).
% 1.25/0.52  fof(f101,plain,(
% 1.25/0.52    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 1.25/0.52    inference(backward_demodulation,[],[f28,f97])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f14])).
% 1.25/0.52  fof(f817,plain,(
% 1.25/0.52    sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 1.25/0.52    inference(forward_demodulation,[],[f816,f131])).
% 1.25/0.52  fof(f816,plain,(
% 1.25/0.52    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,sK3(sK1,sK0))),
% 1.25/0.52    inference(forward_demodulation,[],[f805,f590])).
% 1.25/0.52  fof(f805,plain,(
% 1.25/0.52    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 1.25/0.52    inference(resolution,[],[f402,f32])).
% 1.25/0.52  fof(f402,plain,(
% 1.25/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f401,f137])).
% 1.25/0.52  fof(f137,plain,(
% 1.25/0.52    v1_funct_1(k4_relat_1(sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f136,f30])).
% 1.25/0.52  fof(f136,plain,(
% 1.25/0.52    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 1.25/0.52    inference(subsumption_resolution,[],[f135,f29])).
% 1.25/0.52  fof(f135,plain,(
% 1.25/0.52    v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 1.25/0.52    inference(superposition,[],[f42,f97])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f18])).
% 1.25/0.52  fof(f18,plain,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.25/0.52  fof(f401,plain,(
% 1.25/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f400,f100])).
% 1.25/0.52  fof(f100,plain,(
% 1.25/0.52    v1_relat_1(k4_relat_1(sK1))),
% 1.25/0.52    inference(backward_demodulation,[],[f88,f97])).
% 1.25/0.52  fof(f88,plain,(
% 1.25/0.52    v1_relat_1(k2_funct_1(sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f75,f29])).
% 1.25/0.52  fof(f75,plain,(
% 1.25/0.52    ~v1_relat_1(sK1) | v1_relat_1(k2_funct_1(sK1))),
% 1.25/0.52    inference(resolution,[],[f30,f41])).
% 1.25/0.52  fof(f41,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f400,plain,(
% 1.25/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f399,f30])).
% 1.25/0.53  fof(f399,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) )),
% 1.25/0.53    inference(subsumption_resolution,[],[f391,f29])).
% 1.25/0.53  fof(f391,plain,(
% 1.25/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) )),
% 1.25/0.53    inference(superposition,[],[f52,f386])).
% 1.25/0.53  fof(f386,plain,(
% 1.25/0.53    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))),
% 1.25/0.53    inference(backward_demodulation,[],[f307,f385])).
% 1.25/0.53  fof(f385,plain,(
% 1.25/0.53    k2_relat_1(sK1) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))),
% 1.25/0.53    inference(forward_demodulation,[],[f376,f58])).
% 1.25/0.53  fof(f58,plain,(
% 1.25/0.53    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 1.25/0.53    inference(resolution,[],[f29,f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f16])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.25/0.53  fof(f376,plain,(
% 1.25/0.53    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))),
% 1.25/0.53    inference(superposition,[],[f374,f121])).
% 1.25/0.53  fof(f121,plain,(
% 1.25/0.53    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))),
% 1.25/0.53    inference(forward_demodulation,[],[f103,f59])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))),
% 1.25/0.53    inference(resolution,[],[f29,f39])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f16])).
% 1.25/0.53  fof(f103,plain,(
% 1.25/0.53    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k2_relat_1(k4_relat_1(sK1))))),
% 1.25/0.53    inference(resolution,[],[f100,f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.25/0.53  fof(f374,plain,(
% 1.25/0.53    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0)) )),
% 1.25/0.53    inference(forward_demodulation,[],[f369,f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.25/0.53  fof(f369,plain,(
% 1.25/0.53    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0)))) )),
% 1.25/0.53    inference(resolution,[],[f106,f33])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.25/0.53  fof(f106,plain,(
% 1.25/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(X0))) )),
% 1.25/0.53    inference(resolution,[],[f100,f40])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f1])).
% 1.25/0.53  % (15241)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.25/0.53  fof(f307,plain,(
% 1.25/0.53    k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))),
% 1.25/0.53    inference(resolution,[],[f61,f100])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,sK1)) = k10_relat_1(X1,k1_relat_1(sK1))) )),
% 1.25/0.53    inference(resolution,[],[f29,f40])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(flattening,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (15244)------------------------------
% 1.25/0.53  % (15244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (15244)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (15244)Memory used [KB]: 2046
% 1.25/0.53  % (15244)Time elapsed: 0.097 s
% 1.25/0.53  % (15244)------------------------------
% 1.25/0.53  % (15244)------------------------------
% 1.25/0.53  % (15243)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (15242)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.25/0.53  % (15230)Success in time 0.156 s
%------------------------------------------------------------------------------
