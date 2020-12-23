%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 (10138 expanded)
%              Number of leaves         :   27 (2803 expanded)
%              Depth                    :   41
%              Number of atoms          :  272 (26931 expanded)
%              Number of equality atoms :  141 (7863 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(subsumption_resolution,[],[f668,f111])).

fof(f111,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f87,f107])).

fof(f107,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f89,f101])).

fof(f101,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f97,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f97,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f95,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f94,f86])).

fof(f86,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f94,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f90,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f90,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f43,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f25])).

% (26683)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f89,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f43,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f87,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f44,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f44,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f668,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f620,f666])).

fof(f666,plain,(
    sK0 = k5_xboole_0(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f619,f665])).

fof(f665,plain,(
    sK0 = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f664,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f664,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f600,f139])).

fof(f139,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f109,f50])).

fof(f109,plain,(
    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f100,f107])).

fof(f100,plain,(
    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f98,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f98,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f81,f89])).

fof(f81,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f600,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f570,f584])).

fof(f584,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f575,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f575,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f522,f170])).

fof(f170,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),X0) ),
    inference(backward_demodulation,[],[f169,f165])).

fof(f165,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f128,f158])).

fof(f158,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f138,f50])).

fof(f138,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f136,f60])).

fof(f136,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f135,f86])).

fof(f135,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f129,plain,
    ( r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f116,f56])).

fof(f116,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f61,f107])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f128,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f116,f83])).

fof(f169,plain,(
    ! [X0] : k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f164,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f164,plain,(
    ! [X0] : k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) ),
    inference(backward_demodulation,[],[f155,f158])).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),X0)) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),X0) ),
    inference(superposition,[],[f69,f128])).

fof(f522,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f511,f48])).

fof(f511,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f310,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f310,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f305,f69])).

fof(f305,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) = k5_xboole_0(sK0,X0) ),
    inference(superposition,[],[f69,f297])).

fof(f297,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f295,f158])).

fof(f295,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f286,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f286,plain,(
    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f285,f48])).

fof(f285,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f284,f47])).

fof(f284,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f283,f48])).

fof(f283,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f269,f47])).

fof(f269,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f171,f256])).

fof(f256,plain,(
    ! [X2] : k5_xboole_0(X2,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f170,f51])).

fof(f171,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f168,f165])).

fof(f168,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f167,f69])).

fof(f167,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f166,f158])).

fof(f166,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f163,f51])).

fof(f163,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f156,f158])).

fof(f156,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f82,f128])).

fof(f570,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(superposition,[],[f457,f51])).

fof(f457,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),sK0) ),
    inference(forward_demodulation,[],[f456,f299])).

fof(f299,plain,(
    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f297,f170])).

fof(f456,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f447,f51])).

fof(f447,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f232,f423])).

fof(f423,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(X3,X4)))) ),
    inference(superposition,[],[f256,f69])).

fof(f232,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f178,f231])).

fof(f231,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f181,f226])).

fof(f226,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f193,f50])).

fof(f193,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f187,f60])).

fof(f187,plain,(
    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f186,f86])).

fof(f186,plain,(
    r2_hidden(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f182,f45])).

fof(f182,plain,
    ( r2_hidden(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f177,f56])).

fof(f177,plain,(
    m1_subset_1(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f176,f116])).

fof(f176,plain,
    ( m1_subset_1(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f61,f165])).

fof(f181,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ),
    inference(resolution,[],[f177,f83])).

fof(f178,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(resolution,[],[f177,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,X0)),k5_xboole_0(sK1,k3_subset_1(sK0,X0))) ) ),
    inference(forward_demodulation,[],[f122,f50])).

fof(f122,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X0),sK1),k5_xboole_0(sK1,k3_subset_1(sK0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f120,f51])).

fof(f120,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X0),sK1),k5_xboole_0(k3_subset_1(sK0,X0),sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f93,f61])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(X0,sK1)) ) ),
    inference(forward_demodulation,[],[f92,f51])).

fof(f92,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f88,f82])).

fof(f88,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f43,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f619,plain,(
    k5_xboole_0(k1_xboole_0,sK0) = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f598,f139])).

fof(f598,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f457,f584])).

fof(f620,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f203,f619])).

fof(f203,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f144,f202])).

fof(f202,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f196,f139])).

fof(f196,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f134,f43])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X0,k5_xboole_0(sK0,sK1))) ) ),
    inference(forward_demodulation,[],[f133,f51])).

fof(f133,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK0,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f127,f82])).

fof(f127,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f116,f84])).

fof(f144,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f132,f139])).

fof(f132,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f131,f50])).

fof(f131,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f126,f51])).

fof(f126,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f116,f93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (26689)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (26688)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (26696)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (26695)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (26695)Refutation not found, incomplete strategy% (26695)------------------------------
% 0.21/0.54  % (26695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26695)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26695)Memory used [KB]: 6140
% 0.21/0.54  % (26695)Time elapsed: 0.002 s
% 0.21/0.54  % (26695)------------------------------
% 0.21/0.54  % (26695)------------------------------
% 0.21/0.55  % (26688)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f677,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f668,f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f87,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f89,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(superposition,[],[f97,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f95,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f94,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f90,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,axiom,(
% 0.21/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f43,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f25])).
% 0.21/0.55  % (26683)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  fof(f25,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(resolution,[],[f43,f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f62,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f44,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f668,plain,(
% 0.21/0.55    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f620,f666])).
% 0.21/0.55  fof(f666,plain,(
% 0.21/0.55    sK0 = k5_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.55    inference(backward_demodulation,[],[f619,f665])).
% 0.21/0.55  fof(f665,plain,(
% 0.21/0.55    sK0 = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f664,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f664,plain,(
% 0.21/0.55    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f600,f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(superposition,[],[f109,f50])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f100,f107])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.55    inference(resolution,[],[f98,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.55    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    r1_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.55    inference(superposition,[],[f81,f89])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f49,f54])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.55  fof(f600,plain,(
% 0.21/0.55    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.55    inference(backward_demodulation,[],[f570,f584])).
% 0.21/0.55  fof(f584,plain,(
% 0.21/0.55    k5_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.55    inference(forward_demodulation,[],[f575,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.55  fof(f575,plain,(
% 0.21/0.55    k5_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),
% 0.21/0.55    inference(superposition,[],[f522,f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),X0)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f169,f165])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f128,f158])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(superposition,[],[f138,f50])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f136,f60])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f135,f86])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f129,f45])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f116,f56])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f115,f43])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(superposition,[],[f61,f107])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(resolution,[],[f116,f83])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f164,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),X0))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f155,f158])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),X0)) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),X0)) )),
% 0.21/0.55    inference(superposition,[],[f69,f128])).
% 0.21/0.55  fof(f522,plain,(
% 0.21/0.55    k5_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.55    inference(forward_demodulation,[],[f511,f48])).
% 0.21/0.55  fof(f511,plain,(
% 0.21/0.55    k5_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.55    inference(superposition,[],[f310,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.55  fof(f310,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,X0)))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f305,f69])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) = k5_xboole_0(sK0,X0)) )),
% 0.21/0.55    inference(superposition,[],[f69,f297])).
% 0.21/0.55  fof(f297,plain,(
% 0.21/0.55    sK0 = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f295,f158])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    sK0 = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.55    inference(superposition,[],[f286,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f55,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f52,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f68,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f71,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f72,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f73,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f285,f48])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f284,f47])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0))),
% 0.21/0.56    inference(forward_demodulation,[],[f283,f48])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)))),
% 0.21/0.56    inference(forward_demodulation,[],[f269,f47])).
% 0.21/0.56  fof(f269,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 0.21/0.56    inference(backward_demodulation,[],[f171,f256])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    ( ! [X2] : (k5_xboole_0(X2,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X2)))) )),
% 0.21/0.56    inference(superposition,[],[f170,f51])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),
% 0.21/0.56    inference(backward_demodulation,[],[f168,f165])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))))),
% 0.21/0.56    inference(forward_demodulation,[],[f167,f69])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f166,f158])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f163,f51])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(backward_demodulation,[],[f156,f158])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),
% 0.21/0.56    inference(superposition,[],[f82,f128])).
% 0.21/0.56  fof(f570,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))),
% 0.21/0.56    inference(superposition,[],[f457,f51])).
% 0.21/0.56  fof(f457,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),sK0)),
% 0.21/0.56    inference(forward_demodulation,[],[f456,f299])).
% 0.21/0.56  fof(f299,plain,(
% 0.21/0.56    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),
% 0.21/0.56    inference(superposition,[],[f297,f170])).
% 0.21/0.56  fof(f456,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))))),
% 0.21/0.56    inference(forward_demodulation,[],[f447,f51])).
% 0.21/0.56  fof(f447,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)))))),
% 0.21/0.56    inference(backward_demodulation,[],[f232,f423])).
% 0.21/0.56  fof(f423,plain,(
% 0.21/0.56    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(X3,X4))))) )),
% 0.21/0.56    inference(superposition,[],[f256,f69])).
% 0.21/0.56  fof(f232,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))),
% 0.21/0.56    inference(backward_demodulation,[],[f178,f231])).
% 0.21/0.56  fof(f231,plain,(
% 0.21/0.56    k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(backward_demodulation,[],[f181,f226])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(superposition,[],[f193,f50])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.56    inference(resolution,[],[f187,f60])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.56    inference(resolution,[],[f186,f86])).
% 0.21/0.56  fof(f186,plain,(
% 0.21/0.56    r2_hidden(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f182,f45])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    r2_hidden(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(resolution,[],[f177,f56])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    m1_subset_1(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f176,f116])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    m1_subset_1(k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k1_zfmisc_1(sK0)) | ~m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(superposition,[],[f61,f165])).
% 0.21/0.56  fof(f181,plain,(
% 0.21/0.56    k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),
% 0.21/0.56    inference(resolution,[],[f177,f83])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),k5_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))),
% 0.21/0.56    inference(resolution,[],[f177,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,X0)),k5_xboole_0(sK1,k3_subset_1(sK0,X0)))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f122,f50])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ( ! [X0] : (k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X0),sK1),k5_xboole_0(sK1,k3_subset_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f120,f51])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    ( ! [X0] : (k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X0),sK1),k5_xboole_0(k3_subset_1(sK0,X0),sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f93,f61])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(X0,sK1))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f92,f51])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f88,f82])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f43,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f70,f80])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.56    inference(ennf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.56  fof(f619,plain,(
% 0.21/0.56    k5_xboole_0(k1_xboole_0,sK0) = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f598,f139])).
% 0.21/0.56  fof(f598,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.56    inference(backward_demodulation,[],[f457,f584])).
% 0.21/0.56  fof(f620,plain,(
% 0.21/0.56    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.56    inference(backward_demodulation,[],[f203,f619])).
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),
% 0.21/0.56    inference(backward_demodulation,[],[f144,f202])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f196,f139])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(resolution,[],[f134,f43])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X0,k5_xboole_0(sK0,sK1)))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f133,f51])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    ( ! [X0] : (k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK0,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f127,f82])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    ( ! [X0] : (k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f116,f84])).
% 0.21/0.56  fof(f144,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(backward_demodulation,[],[f132,f139])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f131,f50])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f126,f51])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 0.21/0.56    inference(resolution,[],[f116,f93])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (26688)------------------------------
% 0.21/0.56  % (26688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26688)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (26688)Memory used [KB]: 11257
% 0.21/0.56  % (26688)Time elapsed: 0.112 s
% 0.21/0.56  % (26688)------------------------------
% 0.21/0.56  % (26688)------------------------------
% 0.21/0.56  % (26672)Success in time 0.195 s
%------------------------------------------------------------------------------
