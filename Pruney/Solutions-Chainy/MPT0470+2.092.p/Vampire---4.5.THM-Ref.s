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
% DateTime   : Thu Dec  3 12:47:57 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 957 expanded)
%              Number of leaves         :   18 ( 257 expanded)
%              Depth                    :   26
%              Number of atoms          :  257 (2734 expanded)
%              Number of equality atoms :   57 ( 433 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f828,plain,(
    $false ),
    inference(subsumption_resolution,[],[f827,f156])).

fof(f156,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f43,f155])).

fof(f155,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f153,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f153,plain,(
    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f152,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f152,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f151,f80])).

fof(f80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f79,f42])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f78,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f77,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f61,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f151,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f129,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f129,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f128,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f53,f116])).

fof(f116,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f105,f42])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f104,f89])).

fof(f89,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f59,f78])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f104,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f103,f80])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f43,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f827,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f803,f706])).

fof(f706,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f697,f207])).

fof(f207,plain,(
    k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f205,f47])).

fof(f205,plain,(
    v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f204,f80])).

fof(f204,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f203,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f203,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f202,f80])).

fof(f202,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f186,f56])).

fof(f186,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f185,f44])).

fof(f185,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f53,f176])).

fof(f176,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(resolution,[],[f113,f80])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0)) ) ),
    inference(resolution,[],[f105,f48])).

fof(f697,plain,(
    k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(resolution,[],[f646,f80])).

fof(f646,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k4_relat_1(X0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0)) ) ),
    inference(forward_demodulation,[],[f637,f84])).

fof(f84,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f637,plain,(
    ! [X0] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f172,f80])).

fof(f172,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(k4_relat_1(X2),X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(k4_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f51,f48])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f803,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f370,f802])).

fof(f802,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f724,f225])).

fof(f225,plain,(
    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(resolution,[],[f223,f47])).

fof(f223,plain,(
    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f222,f42])).

fof(f222,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f221,f48])).

fof(f221,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f220,f80])).

fof(f220,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f192,f56])).

fof(f192,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f191,f44])).

fof(f191,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[],[f53,f180])).

fof(f180,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(resolution,[],[f113,f42])).

fof(f724,plain,(
    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f529,f706])).

fof(f529,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f171,f42])).

fof(f171,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f51,f80])).

fof(f370,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f288,f42])).

fof(f288,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k1_xboole_0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f76,f80])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f56,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.54  % (31329)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (31344)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (31336)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.57  % (31328)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.58  % (31346)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.69/0.58  % (31325)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.69/0.58  % (31346)Refutation not found, incomplete strategy% (31346)------------------------------
% 1.69/0.58  % (31346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (31337)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.69/0.58  % (31346)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (31346)Memory used [KB]: 10618
% 1.69/0.58  % (31346)Time elapsed: 0.085 s
% 1.69/0.58  % (31346)------------------------------
% 1.69/0.58  % (31346)------------------------------
% 1.69/0.59  % (31324)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.69/0.59  % (31330)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.69/0.59  % (31322)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.69/0.59  % (31327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.69/0.59  % (31323)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.59  % (31353)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.59  % (31343)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.69/0.59  % (31334)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.60  % (31351)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.88/0.60  % (31347)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.88/0.60  % (31345)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.88/0.60  % (31350)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.88/0.61  % (31340)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.88/0.61  % (31338)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.88/0.61  % (31349)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.88/0.61  % (31341)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.88/0.61  % (31335)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.88/0.61  % (31342)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.88/0.61  % (31341)Refutation not found, incomplete strategy% (31341)------------------------------
% 1.88/0.61  % (31341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (31341)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (31341)Memory used [KB]: 10618
% 1.88/0.61  % (31341)Time elapsed: 0.192 s
% 1.88/0.61  % (31341)------------------------------
% 1.88/0.61  % (31341)------------------------------
% 1.88/0.61  % (31348)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.88/0.61  % (31331)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.88/0.62  % (31330)Refutation found. Thanks to Tanya!
% 1.88/0.62  % SZS status Theorem for theBenchmark
% 1.88/0.62  % SZS output start Proof for theBenchmark
% 1.88/0.62  fof(f828,plain,(
% 1.88/0.62    $false),
% 1.88/0.62    inference(subsumption_resolution,[],[f827,f156])).
% 1.88/0.62  fof(f156,plain,(
% 1.88/0.62    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.88/0.62    inference(subsumption_resolution,[],[f43,f155])).
% 1.88/0.62  fof(f155,plain,(
% 1.88/0.62    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.88/0.62    inference(resolution,[],[f153,f47])).
% 1.88/0.62  fof(f47,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.88/0.62    inference(cnf_transformation,[],[f18])).
% 1.88/0.62  fof(f18,plain,(
% 1.88/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f4])).
% 1.88/0.62  fof(f4,axiom,(
% 1.88/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.88/0.62  fof(f153,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f152,f42])).
% 1.88/0.62  fof(f42,plain,(
% 1.88/0.62    v1_relat_1(sK0)),
% 1.88/0.62    inference(cnf_transformation,[],[f30])).
% 1.88/0.62  fof(f30,plain,(
% 1.88/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.88/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).
% 1.88/0.62  fof(f29,plain,(
% 1.88/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.88/0.62    introduced(choice_axiom,[])).
% 1.88/0.62  fof(f17,plain,(
% 1.88/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f16])).
% 1.88/0.62  fof(f16,negated_conjecture,(
% 1.88/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.88/0.62    inference(negated_conjecture,[],[f15])).
% 1.88/0.62  fof(f15,conjecture,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.88/0.62  fof(f152,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.88/0.62    inference(subsumption_resolution,[],[f151,f80])).
% 1.88/0.62  fof(f80,plain,(
% 1.88/0.62    v1_relat_1(k1_xboole_0)),
% 1.88/0.62    inference(resolution,[],[f79,f42])).
% 1.88/0.62  fof(f79,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k1_xboole_0)) )),
% 1.88/0.62    inference(resolution,[],[f78,f74])).
% 1.88/0.62  fof(f74,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.88/0.62    inference(resolution,[],[f52,f64])).
% 1.88/0.62  fof(f64,plain,(
% 1.88/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f41])).
% 1.88/0.62  fof(f41,plain,(
% 1.88/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.88/0.62    inference(nnf_transformation,[],[f6])).
% 1.88/0.62  fof(f6,axiom,(
% 1.88/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.88/0.62  fof(f52,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f23])).
% 1.88/0.62  fof(f23,plain,(
% 1.88/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f7])).
% 1.88/0.62  fof(f7,axiom,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.88/0.62  fof(f78,plain,(
% 1.88/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.88/0.62    inference(resolution,[],[f77,f44])).
% 1.88/0.62  fof(f44,plain,(
% 1.88/0.62    v1_xboole_0(k1_xboole_0)),
% 1.88/0.62    inference(cnf_transformation,[],[f3])).
% 1.88/0.62  fof(f3,axiom,(
% 1.88/0.62    v1_xboole_0(k1_xboole_0)),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.88/0.62  fof(f77,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.88/0.62    inference(resolution,[],[f61,f54])).
% 1.88/0.62  fof(f54,plain,(
% 1.88/0.62    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f34])).
% 1.88/0.62  fof(f34,plain,(
% 1.88/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.88/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 1.88/0.62  fof(f33,plain,(
% 1.88/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.88/0.62    introduced(choice_axiom,[])).
% 1.88/0.62  fof(f32,plain,(
% 1.88/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.88/0.62    inference(rectify,[],[f31])).
% 1.88/0.62  fof(f31,plain,(
% 1.88/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.88/0.62    inference(nnf_transformation,[],[f1])).
% 1.88/0.62  fof(f1,axiom,(
% 1.88/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.88/0.62  fof(f61,plain,(
% 1.88/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f40])).
% 1.88/0.62  fof(f40,plain,(
% 1.88/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.88/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.88/0.62  fof(f39,plain,(
% 1.88/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.88/0.62    introduced(choice_axiom,[])).
% 1.88/0.62  fof(f38,plain,(
% 1.88/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.88/0.62    inference(rectify,[],[f37])).
% 1.88/0.62  fof(f37,plain,(
% 1.88/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.88/0.62    inference(nnf_transformation,[],[f28])).
% 1.88/0.62  fof(f28,plain,(
% 1.88/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.88/0.62    inference(ennf_transformation,[],[f2])).
% 1.88/0.62  fof(f2,axiom,(
% 1.88/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.88/0.62  fof(f151,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.88/0.62    inference(resolution,[],[f129,f56])).
% 1.88/0.62  fof(f56,plain,(
% 1.88/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f27])).
% 1.88/0.62  fof(f27,plain,(
% 1.88/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.88/0.62    inference(flattening,[],[f26])).
% 1.88/0.62  fof(f26,plain,(
% 1.88/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.88/0.62    inference(ennf_transformation,[],[f9])).
% 1.88/0.62  fof(f9,axiom,(
% 1.88/0.62    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.88/0.62  fof(f129,plain,(
% 1.88/0.62    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f128,f44])).
% 1.88/0.62  fof(f128,plain,(
% 1.88/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.88/0.62    inference(superposition,[],[f53,f116])).
% 1.88/0.62  fof(f116,plain,(
% 1.88/0.62    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f105,f42])).
% 1.88/0.62  fof(f105,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.88/0.62    inference(resolution,[],[f104,f89])).
% 1.88/0.62  fof(f89,plain,(
% 1.88/0.62    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.88/0.62    inference(resolution,[],[f59,f78])).
% 1.88/0.62  fof(f59,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.88/0.62    inference(cnf_transformation,[],[f36])).
% 1.88/0.62  fof(f36,plain,(
% 1.88/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/0.62    inference(flattening,[],[f35])).
% 1.88/0.62  fof(f35,plain,(
% 1.88/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/0.62    inference(nnf_transformation,[],[f5])).
% 1.88/0.62  fof(f5,axiom,(
% 1.88/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.88/0.62  fof(f104,plain,(
% 1.88/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(subsumption_resolution,[],[f103,f80])).
% 1.88/0.62  fof(f103,plain,(
% 1.88/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(superposition,[],[f50,f46])).
% 1.88/0.62  fof(f46,plain,(
% 1.88/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.88/0.62    inference(cnf_transformation,[],[f14])).
% 1.88/0.62  fof(f14,axiom,(
% 1.88/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.88/0.62  fof(f50,plain,(
% 1.88/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f21])).
% 1.88/0.62  fof(f21,plain,(
% 1.88/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f12])).
% 1.88/0.62  fof(f12,axiom,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.88/0.62  fof(f53,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f25])).
% 1.88/0.62  fof(f25,plain,(
% 1.88/0.62    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.88/0.62    inference(flattening,[],[f24])).
% 1.88/0.62  fof(f24,plain,(
% 1.88/0.62    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.88/0.62    inference(ennf_transformation,[],[f10])).
% 1.88/0.62  fof(f10,axiom,(
% 1.88/0.62    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.88/0.62  fof(f43,plain,(
% 1.88/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.88/0.62    inference(cnf_transformation,[],[f30])).
% 1.88/0.62  fof(f827,plain,(
% 1.88/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.88/0.62    inference(forward_demodulation,[],[f803,f706])).
% 1.88/0.62  fof(f706,plain,(
% 1.88/0.62    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.88/0.62    inference(forward_demodulation,[],[f697,f207])).
% 1.88/0.62  fof(f207,plain,(
% 1.88/0.62    k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.88/0.62    inference(resolution,[],[f205,f47])).
% 1.88/0.62  fof(f205,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f204,f80])).
% 1.88/0.62  fof(f204,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.88/0.62    inference(resolution,[],[f203,f48])).
% 1.88/0.62  fof(f48,plain,(
% 1.88/0.62    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f19])).
% 1.88/0.62  fof(f19,plain,(
% 1.88/0.62    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f8])).
% 1.88/0.62  fof(f8,axiom,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.88/0.62  fof(f203,plain,(
% 1.88/0.62    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f202,f80])).
% 1.88/0.62  fof(f202,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f186,f56])).
% 1.88/0.62  fof(f186,plain,(
% 1.88/0.62    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f185,f44])).
% 1.88/0.62  fof(f185,plain,(
% 1.88/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.88/0.62    inference(superposition,[],[f53,f176])).
% 1.88/0.62  fof(f176,plain,(
% 1.88/0.62    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f113,f80])).
% 1.88/0.62  fof(f113,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))) )),
% 1.88/0.62    inference(resolution,[],[f105,f48])).
% 1.88/0.62  fof(f697,plain,(
% 1.88/0.62    k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f646,f80])).
% 1.88/0.62  fof(f646,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k4_relat_1(X0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0))) )),
% 1.88/0.62    inference(forward_demodulation,[],[f637,f84])).
% 1.88/0.62  fof(f84,plain,(
% 1.88/0.62    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f80,f49])).
% 1.88/0.62  fof(f49,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.88/0.62    inference(cnf_transformation,[],[f20])).
% 1.88/0.62  fof(f20,plain,(
% 1.88/0.62    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f11])).
% 1.88/0.62  fof(f11,axiom,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.88/0.62  fof(f637,plain,(
% 1.88/0.62    ( ! [X0] : (k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(X0)) )),
% 1.88/0.62    inference(resolution,[],[f172,f80])).
% 1.88/0.62  fof(f172,plain,(
% 1.88/0.62    ( ! [X2,X1] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k4_relat_1(X2),X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(k4_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 1.88/0.62    inference(resolution,[],[f51,f48])).
% 1.88/0.62  fof(f51,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f22])).
% 1.88/0.62  fof(f22,plain,(
% 1.88/0.62    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.88/0.62    inference(ennf_transformation,[],[f13])).
% 1.88/0.62  fof(f13,axiom,(
% 1.88/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.88/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.88/0.62  fof(f803,plain,(
% 1.88/0.62    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)),
% 1.88/0.62    inference(backward_demodulation,[],[f370,f802])).
% 1.88/0.62  fof(f802,plain,(
% 1.88/0.62    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.88/0.62    inference(forward_demodulation,[],[f724,f225])).
% 1.88/0.62  fof(f225,plain,(
% 1.88/0.62    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 1.88/0.62    inference(resolution,[],[f223,f47])).
% 1.88/0.62  fof(f223,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f222,f42])).
% 1.88/0.62  fof(f222,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.88/0.62    inference(resolution,[],[f221,f48])).
% 1.88/0.62  fof(f221,plain,(
% 1.88/0.62    ~v1_relat_1(k4_relat_1(sK0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f220,f80])).
% 1.88/0.62  fof(f220,plain,(
% 1.88/0.62    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0))),
% 1.88/0.62    inference(resolution,[],[f192,f56])).
% 1.88/0.62  fof(f192,plain,(
% 1.88/0.62    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.88/0.62    inference(subsumption_resolution,[],[f191,f44])).
% 1.88/0.62  fof(f191,plain,(
% 1.88/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.88/0.62    inference(superposition,[],[f53,f180])).
% 1.88/0.62  fof(f180,plain,(
% 1.88/0.62    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f113,f42])).
% 1.88/0.62  fof(f724,plain,(
% 1.88/0.62    k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.88/0.62    inference(backward_demodulation,[],[f529,f706])).
% 1.88/0.62  fof(f529,plain,(
% 1.88/0.62    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))),
% 1.88/0.62    inference(resolution,[],[f171,f42])).
% 1.88/0.62  fof(f171,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))) )),
% 1.88/0.62    inference(resolution,[],[f51,f80])).
% 1.88/0.62  fof(f370,plain,(
% 1.88/0.62    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 1.88/0.62    inference(resolution,[],[f288,f42])).
% 1.88/0.62  fof(f288,plain,(
% 1.88/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k1_xboole_0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X0)))) )),
% 1.88/0.62    inference(resolution,[],[f76,f80])).
% 1.88/0.62  fof(f76,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) )),
% 1.88/0.62    inference(resolution,[],[f56,f49])).
% 1.88/0.62  % SZS output end Proof for theBenchmark
% 1.88/0.62  % (31330)------------------------------
% 1.88/0.62  % (31330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (31330)Termination reason: Refutation
% 1.88/0.62  
% 1.88/0.62  % (31330)Memory used [KB]: 6908
% 1.88/0.62  % (31330)Time elapsed: 0.131 s
% 1.88/0.62  % (31330)------------------------------
% 1.88/0.62  % (31330)------------------------------
% 1.88/0.62  % (31355)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.88/0.62  % (31332)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.88/0.63  % (31317)Success in time 0.267 s
%------------------------------------------------------------------------------
