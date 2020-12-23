%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:54 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  134 (3000 expanded)
%              Number of leaves         :   17 ( 803 expanded)
%              Depth                    :   30
%              Number of atoms          :  256 (6024 expanded)
%              Number of equality atoms :  115 (1518 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f672,plain,(
    $false ),
    inference(subsumption_resolution,[],[f671,f600])).

fof(f600,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f42,f599])).

fof(f599,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f582,f108])).

fof(f108,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f98,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f98,plain,(
    v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f97,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f97,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f95,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f94,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f94,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f93,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f57,f92])).

fof(f92,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f91,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f91,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f582,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f254,f580])).

fof(f580,plain,(
    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f579,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f579,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f574,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f574,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k2_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f318,f571])).

% (26968)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f571,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f549,f41])).

fof(f41,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f37])).

fof(f37,plain,
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

% (26982)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

% (26983)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f549,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f548,f44])).

fof(f548,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f547,f99])).

fof(f99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f78,f98])).

fof(f78,plain,
    ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f50,f75])).

fof(f75,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f71,f43])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f51,f48])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f547,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f537,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f537,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f56,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

% (26976)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f318,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k2_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(forward_demodulation,[],[f317,f281])).

fof(f281,plain,(
    k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f267,f247])).

fof(f247,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(resolution,[],[f236,f41])).

fof(f236,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f232,f108])).

fof(f232,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f55,f99])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f267,plain,(
    k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f263,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f263,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f261,f41])).

fof(f261,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f260,f50])).

fof(f260,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f258,f99])).

fof(f258,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f253,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f253,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f237,f247])).

fof(f237,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f50,f230])).

fof(f230,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f210,f41])).

fof(f210,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2))) ) ),
    inference(resolution,[],[f88,f99])).

fof(f88,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | k5_relat_1(X5,X4) = k4_relat_1(k4_relat_1(k5_relat_1(X5,X4))) ) ),
    inference(resolution,[],[f60,f51])).

fof(f317,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(forward_demodulation,[],[f302,f282])).

fof(f282,plain,(
    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f268,f247])).

fof(f268,plain,(
    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f263,f54])).

fof(f302,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) ),
    inference(resolution,[],[f264,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f264,plain,(
    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f256,f263])).

fof(f256,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f50,f247])).

fof(f254,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f230,f247])).

fof(f42,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f671,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f653,f108])).

fof(f653,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f355,f651])).

fof(f651,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f650,f47])).

fof(f650,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f648,f68])).

fof(f68,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f648,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_xboole_0,k1_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(backward_demodulation,[],[f424,f645])).

fof(f645,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f385,f640])).

fof(f640,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f563,f41])).

fof(f563,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X1))) ) ),
    inference(resolution,[],[f549,f50])).

fof(f385,plain,(
    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f370,f352])).

fof(f352,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f346,f108])).

fof(f346,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) ),
    inference(resolution,[],[f235,f99])).

fof(f235,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k4_relat_1(k5_relat_1(sK0,X8)) = k5_relat_1(k4_relat_1(X8),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f55,f41])).

fof(f370,plain,(
    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f366,f53])).

fof(f366,plain,(
    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f364,f41])).

fof(f364,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f363,f50])).

fof(f363,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f361,f99])).

fof(f361,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f354,f60])).

fof(f354,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f222,f352])).

fof(f222,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f50,f215])).

fof(f215,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f213,f99])).

fof(f213,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(sK0,X8) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X8))) ) ),
    inference(resolution,[],[f88,f41])).

fof(f424,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f423,f385])).

fof(f423,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f407,f386])).

fof(f386,plain,(
    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f371,f352])).

fof(f371,plain,(
    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f366,f54])).

fof(f407,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))) ),
    inference(resolution,[],[f367,f52])).

fof(f367,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f359,f366])).

fof(f359,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f50,f352])).

fof(f355,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f215,f352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.51  % (26965)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (26970)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (26957)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (26962)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (26978)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (26955)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (26973)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (26977)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (26969)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.60/0.56  % (26977)Refutation not found, incomplete strategy% (26977)------------------------------
% 1.60/0.56  % (26977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.56  % (26977)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.56  
% 1.60/0.56  % (26977)Memory used [KB]: 10746
% 1.60/0.56  % (26977)Time elapsed: 0.078 s
% 1.60/0.56  % (26977)------------------------------
% 1.60/0.56  % (26977)------------------------------
% 1.60/0.56  % (26959)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.60/0.57  % (26979)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.57  % (26961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.60/0.57  % (26971)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.60/0.58  % (26984)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.60/0.58  % (26960)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.73/0.58  % (26964)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.73/0.59  % (26962)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.73/0.59  % (26958)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.73/0.59  % (26956)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f672,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(subsumption_resolution,[],[f671,f600])).
% 1.73/0.59  fof(f600,plain,(
% 1.73/0.59    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f42,f599])).
% 1.73/0.59  fof(f599,plain,(
% 1.73/0.59    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.73/0.59    inference(forward_demodulation,[],[f582,f108])).
% 1.73/0.59  fof(f108,plain,(
% 1.73/0.59    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.73/0.59    inference(resolution,[],[f98,f49])).
% 1.73/0.59  fof(f49,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f25])).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f2])).
% 1.73/0.59  fof(f2,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.73/0.59  fof(f98,plain,(
% 1.73/0.59    v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(subsumption_resolution,[],[f97,f43])).
% 1.73/0.59  fof(f43,plain,(
% 1.73/0.59    v1_xboole_0(k1_xboole_0)),
% 1.73/0.59    inference(cnf_transformation,[],[f1])).
% 1.73/0.59  fof(f1,axiom,(
% 1.73/0.59    v1_xboole_0(k1_xboole_0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.73/0.59  fof(f97,plain,(
% 1.73/0.59    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 1.73/0.59    inference(resolution,[],[f95,f48])).
% 1.73/0.59  fof(f48,plain,(
% 1.73/0.59    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f24])).
% 1.73/0.59  fof(f24,plain,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.73/0.59  fof(f95,plain,(
% 1.73/0.59    ~v1_relat_1(k1_xboole_0) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(resolution,[],[f94,f50])).
% 1.73/0.59  fof(f50,plain,(
% 1.73/0.59    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f26])).
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f12])).
% 1.73/0.59  fof(f12,axiom,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.73/0.59  fof(f94,plain,(
% 1.73/0.59    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(subsumption_resolution,[],[f93,f43])).
% 1.73/0.59  fof(f93,plain,(
% 1.73/0.59    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(superposition,[],[f57,f92])).
% 1.73/0.59  fof(f92,plain,(
% 1.73/0.59    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(forward_demodulation,[],[f91,f44])).
% 1.73/0.59  fof(f44,plain,(
% 1.73/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.73/0.59    inference(cnf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,axiom,(
% 1.73/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.73/0.59  fof(f91,plain,(
% 1.73/0.59    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(resolution,[],[f83,f43])).
% 1.73/0.59  fof(f83,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.73/0.59    inference(resolution,[],[f54,f48])).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f17])).
% 1.73/0.59  fof(f17,axiom,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.73/0.59  fof(f57,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f34])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.73/0.59    inference(flattening,[],[f33])).
% 1.73/0.59  fof(f33,plain,(
% 1.73/0.59    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f14])).
% 1.73/0.59  fof(f14,axiom,(
% 1.73/0.59    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.73/0.59  fof(f582,plain,(
% 1.73/0.59    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)),
% 1.73/0.59    inference(backward_demodulation,[],[f254,f580])).
% 1.73/0.59  fof(f580,plain,(
% 1.73/0.59    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 1.73/0.59    inference(forward_demodulation,[],[f579,f47])).
% 1.73/0.59  fof(f47,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.73/0.59  fof(f579,plain,(
% 1.73/0.59    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k1_xboole_0)),
% 1.73/0.59    inference(forward_demodulation,[],[f574,f67])).
% 1.73/0.59  fof(f67,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.73/0.59    inference(equality_resolution,[],[f63])).
% 1.73/0.59  fof(f63,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f40])).
% 1.73/0.59  fof(f40,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.73/0.59    inference(flattening,[],[f39])).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.73/0.59    inference(nnf_transformation,[],[f9])).
% 1.73/0.59  fof(f9,axiom,(
% 1.73/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.73/0.59  fof(f574,plain,(
% 1.73/0.59    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k2_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0))),
% 1.73/0.59    inference(backward_demodulation,[],[f318,f571])).
% 1.73/0.59  % (26968)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.73/0.59  fof(f571,plain,(
% 1.73/0.59    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.73/0.59    inference(resolution,[],[f549,f41])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    v1_relat_1(sK0)),
% 1.73/0.59    inference(cnf_transformation,[],[f38])).
% 1.73/0.59  fof(f38,plain,(
% 1.73/0.59    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f37])).
% 1.73/0.59  fof(f37,plain,(
% 1.73/0.59    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f23,plain,(
% 1.73/0.59    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f22])).
% 1.73/0.59  % (26982)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.73/0.59  fof(f22,negated_conjecture,(
% 1.73/0.59    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.73/0.59    inference(negated_conjecture,[],[f21])).
% 1.73/0.59  % (26983)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.73/0.59  fof(f21,conjecture,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.73/0.59  fof(f549,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.73/0.59    inference(forward_demodulation,[],[f548,f44])).
% 1.73/0.59  fof(f548,plain,(
% 1.73/0.59    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f547,f99])).
% 1.73/0.59  fof(f99,plain,(
% 1.73/0.59    v1_relat_1(k1_xboole_0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f78,f98])).
% 1.73/0.59  fof(f78,plain,(
% 1.73/0.59    ~v1_xboole_0(k4_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0)),
% 1.73/0.59    inference(resolution,[],[f76,f48])).
% 1.73/0.59  fof(f76,plain,(
% 1.73/0.59    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0)),
% 1.73/0.59    inference(superposition,[],[f50,f75])).
% 1.73/0.59  fof(f75,plain,(
% 1.73/0.59    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 1.73/0.59    inference(resolution,[],[f71,f43])).
% 1.73/0.59  fof(f71,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.73/0.59    inference(resolution,[],[f51,f48])).
% 1.73/0.59  fof(f51,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.73/0.59    inference(cnf_transformation,[],[f27])).
% 1.73/0.59  fof(f27,plain,(
% 1.73/0.59    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f15])).
% 1.73/0.59  fof(f15,axiom,(
% 1.73/0.59    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.73/0.59  fof(f547,plain,(
% 1.73/0.59    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f537,f46])).
% 1.73/0.59  fof(f46,plain,(
% 1.73/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.73/0.59  fof(f537,plain,(
% 1.73/0.59    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.73/0.59    inference(superposition,[],[f56,f45])).
% 1.73/0.60  fof(f45,plain,(
% 1.73/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.73/0.60    inference(cnf_transformation,[],[f20])).
% 1.73/0.60  fof(f56,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f32])).
% 1.73/0.60  fof(f32,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(flattening,[],[f31])).
% 1.73/0.60  fof(f31,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f18])).
% 1.73/0.60  fof(f18,axiom,(
% 1.73/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.73/0.60  % (26976)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.73/0.60  fof(f318,plain,(
% 1.73/0.60    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k2_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 1.73/0.60    inference(forward_demodulation,[],[f317,f281])).
% 1.73/0.60  fof(f281,plain,(
% 1.73/0.60    k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.73/0.60    inference(forward_demodulation,[],[f267,f247])).
% 1.73/0.60  fof(f247,plain,(
% 1.73/0.60    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 1.73/0.60    inference(resolution,[],[f236,f41])).
% 1.73/0.60  fof(f236,plain,(
% 1.73/0.60    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0)) )),
% 1.73/0.60    inference(forward_demodulation,[],[f232,f108])).
% 1.73/0.60  fof(f232,plain,(
% 1.73/0.60    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k1_xboole_0,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k1_xboole_0))) )),
% 1.73/0.60    inference(resolution,[],[f55,f99])).
% 1.73/0.60  fof(f55,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f30])).
% 1.73/0.60  fof(f30,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f19])).
% 1.73/0.60  fof(f19,axiom,(
% 1.73/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.73/0.60  fof(f267,plain,(
% 1.73/0.60    k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 1.73/0.60    inference(resolution,[],[f263,f53])).
% 1.73/0.60  fof(f53,plain,(
% 1.73/0.60    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f29])).
% 1.73/0.60  fof(f263,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.73/0.60    inference(subsumption_resolution,[],[f261,f41])).
% 1.73/0.60  fof(f261,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(sK0)),
% 1.73/0.60    inference(resolution,[],[f260,f50])).
% 1.73/0.60  fof(f260,plain,(
% 1.73/0.60    ~v1_relat_1(k4_relat_1(sK0)) | v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.73/0.60    inference(subsumption_resolution,[],[f258,f99])).
% 1.73/0.60  fof(f258,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0))),
% 1.73/0.60    inference(resolution,[],[f253,f60])).
% 1.73/0.60  fof(f60,plain,(
% 1.73/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f36])).
% 1.73/0.60  fof(f36,plain,(
% 1.73/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(flattening,[],[f35])).
% 1.73/0.60  fof(f35,plain,(
% 1.73/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f13])).
% 1.73/0.60  fof(f13,axiom,(
% 1.73/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.73/0.60  fof(f253,plain,(
% 1.73/0.60    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.73/0.60    inference(backward_demodulation,[],[f237,f247])).
% 1.73/0.60  fof(f237,plain,(
% 1.73/0.60    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.73/0.60    inference(superposition,[],[f50,f230])).
% 1.73/0.60  fof(f230,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 1.73/0.60    inference(resolution,[],[f210,f41])).
% 1.73/0.60  fof(f210,plain,(
% 1.73/0.60    ( ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2)))) )),
% 1.73/0.60    inference(resolution,[],[f88,f99])).
% 1.73/0.60  fof(f88,plain,(
% 1.73/0.60    ( ! [X4,X5] : (~v1_relat_1(X5) | ~v1_relat_1(X4) | k5_relat_1(X5,X4) = k4_relat_1(k4_relat_1(k5_relat_1(X5,X4)))) )),
% 1.73/0.60    inference(resolution,[],[f60,f51])).
% 1.73/0.60  fof(f317,plain,(
% 1.73/0.60    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k1_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 1.73/0.60    inference(forward_demodulation,[],[f302,f282])).
% 1.73/0.60  fof(f282,plain,(
% 1.73/0.60    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.73/0.60    inference(forward_demodulation,[],[f268,f247])).
% 1.73/0.60  fof(f268,plain,(
% 1.73/0.60    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 1.73/0.60    inference(resolution,[],[f263,f54])).
% 1.73/0.60  fof(f302,plain,(
% 1.73/0.60    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k3_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))))),
% 1.73/0.60    inference(resolution,[],[f264,f52])).
% 1.73/0.60  fof(f52,plain,(
% 1.73/0.60    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.73/0.60    inference(cnf_transformation,[],[f28])).
% 1.73/0.60  fof(f28,plain,(
% 1.73/0.60    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f16])).
% 1.73/0.60  fof(f16,axiom,(
% 1.73/0.60    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.73/0.60  fof(f264,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.73/0.60    inference(subsumption_resolution,[],[f256,f263])).
% 1.73/0.60  fof(f256,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.73/0.60    inference(superposition,[],[f50,f247])).
% 1.73/0.60  fof(f254,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.73/0.60    inference(backward_demodulation,[],[f230,f247])).
% 1.73/0.60  fof(f42,plain,(
% 1.73/0.60    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f38])).
% 1.73/0.60  fof(f671,plain,(
% 1.73/0.60    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.73/0.60    inference(forward_demodulation,[],[f653,f108])).
% 1.73/0.60  fof(f653,plain,(
% 1.73/0.60    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)),
% 1.73/0.60    inference(backward_demodulation,[],[f355,f651])).
% 1.73/0.60  fof(f651,plain,(
% 1.73/0.60    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.73/0.60    inference(forward_demodulation,[],[f650,f47])).
% 1.73/0.60  fof(f650,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k1_xboole_0)),
% 1.73/0.60    inference(forward_demodulation,[],[f648,f68])).
% 1.73/0.60  fof(f68,plain,(
% 1.73/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.73/0.60    inference(equality_resolution,[],[f62])).
% 1.73/0.60  fof(f62,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f648,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_xboole_0,k1_relat_1(k5_relat_1(sK0,k1_xboole_0))))),
% 1.73/0.60    inference(backward_demodulation,[],[f424,f645])).
% 1.73/0.60  fof(f645,plain,(
% 1.73/0.60    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.73/0.60    inference(backward_demodulation,[],[f385,f640])).
% 1.73/0.60  fof(f640,plain,(
% 1.73/0.60    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.73/0.60    inference(resolution,[],[f563,f41])).
% 1.73/0.60  fof(f563,plain,(
% 1.73/0.60    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X1)))) )),
% 1.73/0.60    inference(resolution,[],[f549,f50])).
% 1.73/0.60  fof(f385,plain,(
% 1.73/0.60    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.73/0.60    inference(forward_demodulation,[],[f370,f352])).
% 1.73/0.60  fof(f352,plain,(
% 1.73/0.60    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.73/0.60    inference(forward_demodulation,[],[f346,f108])).
% 1.73/0.60  fof(f346,plain,(
% 1.73/0.60    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))),
% 1.73/0.60    inference(resolution,[],[f235,f99])).
% 1.73/0.60  fof(f235,plain,(
% 1.73/0.60    ( ! [X8] : (~v1_relat_1(X8) | k4_relat_1(k5_relat_1(sK0,X8)) = k5_relat_1(k4_relat_1(X8),k4_relat_1(sK0))) )),
% 1.73/0.60    inference(resolution,[],[f55,f41])).
% 1.73/0.60  fof(f370,plain,(
% 1.73/0.60    k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.73/0.60    inference(resolution,[],[f366,f53])).
% 1.73/0.60  fof(f366,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.73/0.60    inference(subsumption_resolution,[],[f364,f41])).
% 1.73/0.60  fof(f364,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.73/0.60    inference(resolution,[],[f363,f50])).
% 1.73/0.60  fof(f363,plain,(
% 1.73/0.60    ~v1_relat_1(k4_relat_1(sK0)) | v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.73/0.60    inference(subsumption_resolution,[],[f361,f99])).
% 1.73/0.60  fof(f361,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.73/0.60    inference(resolution,[],[f354,f60])).
% 1.73/0.60  fof(f354,plain,(
% 1.73/0.60    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.73/0.60    inference(backward_demodulation,[],[f222,f352])).
% 1.73/0.60  fof(f222,plain,(
% 1.73/0.60    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.73/0.60    inference(superposition,[],[f50,f215])).
% 1.73/0.60  fof(f215,plain,(
% 1.73/0.60    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.73/0.60    inference(resolution,[],[f213,f99])).
% 1.73/0.60  fof(f213,plain,(
% 1.73/0.60    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(sK0,X8) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X8)))) )),
% 1.73/0.60    inference(resolution,[],[f88,f41])).
% 1.73/0.60  fof(f424,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_relat_1(k5_relat_1(sK0,k1_xboole_0))))),
% 1.73/0.60    inference(forward_demodulation,[],[f423,f385])).
% 1.73/0.60  fof(f423,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k5_relat_1(sK0,k1_xboole_0))))),
% 1.73/0.60    inference(forward_demodulation,[],[f407,f386])).
% 1.73/0.60  fof(f386,plain,(
% 1.73/0.60    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.73/0.60    inference(forward_demodulation,[],[f371,f352])).
% 1.73/0.60  fof(f371,plain,(
% 1.73/0.60    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.73/0.60    inference(resolution,[],[f366,f54])).
% 1.73/0.60  fof(f407,plain,(
% 1.73/0.60    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k3_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k2_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))))),
% 1.73/0.60    inference(resolution,[],[f367,f52])).
% 1.73/0.60  fof(f367,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.73/0.60    inference(subsumption_resolution,[],[f359,f366])).
% 1.73/0.60  fof(f359,plain,(
% 1.73/0.60    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.73/0.60    inference(superposition,[],[f50,f352])).
% 1.73/0.60  fof(f355,plain,(
% 1.73/0.60    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.73/0.60    inference(backward_demodulation,[],[f215,f352])).
% 1.73/0.60  % SZS output end Proof for theBenchmark
% 1.73/0.60  % (26962)------------------------------
% 1.73/0.60  % (26962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (26962)Termination reason: Refutation
% 1.73/0.60  
% 1.73/0.60  % (26962)Memory used [KB]: 6652
% 1.73/0.60  % (26962)Time elapsed: 0.173 s
% 1.73/0.60  % (26962)------------------------------
% 1.73/0.60  % (26962)------------------------------
% 1.73/0.60  % (26954)Success in time 0.242 s
%------------------------------------------------------------------------------
