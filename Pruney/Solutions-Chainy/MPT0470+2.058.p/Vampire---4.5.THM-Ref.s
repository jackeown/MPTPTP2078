%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 150 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :   24
%              Number of atoms          :  191 ( 359 expanded)
%              Number of equality atoms :   74 ( 156 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f240,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f36,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f240,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f239,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f239,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f237,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f237,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f236,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f236,plain,(
    ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f235,f35])).

fof(f35,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

fof(f235,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | r2_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f234,f84])).

fof(f84,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f32,f83])).

fof(f83,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f82,f50])).

fof(f82,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f81,f39])).

fof(f81,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f79,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f78,f43])).

fof(f78,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f77,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | r2_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f69,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f68,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f68,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f64])).

fof(f64,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f63,f31])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f62,f50])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f61,f39])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f60,f34])).

fof(f34,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f60,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

% (20786)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f32,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f234,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | r2_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f231,f44])).

fof(f231,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f228,f49])).

fof(f49,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f228,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f40,f222])).

fof(f222,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f221,f31])).

fof(f221,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f220,f37])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f219,f34])).

fof(f219,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f218,f33])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f75,f50])).

fof(f75,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X2))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (20787)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (20782)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (20795)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (20782)Refutation not found, incomplete strategy% (20782)------------------------------
% 0.20/0.51  % (20782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20782)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20782)Memory used [KB]: 10618
% 0.20/0.51  % (20782)Time elapsed: 0.085 s
% 0.20/0.51  % (20782)------------------------------
% 0.20/0.51  % (20782)------------------------------
% 0.20/0.52  % (20808)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (20787)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f240,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f36,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f239,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    ~v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f237,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    v1_relat_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f236,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f235,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | r2_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f234,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f32,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f82,f50])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f81,f39])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f79,f31])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.20/0.52    inference(resolution,[],[f78,f43])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f77,f35])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | r2_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f69,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.52    inference(forward_demodulation,[],[f68,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.52    inference(superposition,[],[f40,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.52    inference(resolution,[],[f63,f31])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f50])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f61,f39])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f60,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f58,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  % (20786)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f41,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | r2_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f231,f44])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f228,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.52    inference(superposition,[],[f40,f222])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.52    inference(resolution,[],[f221,f31])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f220,f37])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f219,f34])).
% 0.20/0.52  fof(f219,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f218,f33])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))) )),
% 0.20/0.52    inference(resolution,[],[f75,f50])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~v1_xboole_0(X1) | ~v1_relat_1(X2) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X2)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) )),
% 0.20/0.52    inference(resolution,[],[f42,f39])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (20787)------------------------------
% 0.20/0.52  % (20787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20787)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (20787)Memory used [KB]: 6396
% 0.20/0.52  % (20787)Time elapsed: 0.082 s
% 0.20/0.52  % (20787)------------------------------
% 0.20/0.52  % (20787)------------------------------
% 0.20/0.52  % (20779)Success in time 0.159 s
%------------------------------------------------------------------------------
