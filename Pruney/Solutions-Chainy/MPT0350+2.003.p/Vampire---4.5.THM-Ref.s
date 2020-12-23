%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:50 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  125 (1167 expanded)
%              Number of leaves         :   21 ( 325 expanded)
%              Depth                    :   33
%              Number of atoms          :  214 (3294 expanded)
%              Number of equality atoms :  107 ( 924 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(subsumption_resolution,[],[f647,f111])).

fof(f111,plain,(
    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f86,f106])).

fof(f106,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f52,f93])).

fof(f93,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f92,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f92,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f87,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f83,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f83,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

% (2056)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f77,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f86,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f85,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f84,f82])).

fof(f82,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f76,f75])).

fof(f75,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f76,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f84,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f81,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f81,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f72,f75])).

fof(f72,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f41,f43])).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f647,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f646,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f646,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f368,f645])).

fof(f645,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f636,f149])).

fof(f149,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f127,f147])).

fof(f147,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f124,f142])).

fof(f142,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f48,f135])).

fof(f135,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f134,f118])).

fof(f118,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f49,f97])).

fof(f97,plain,(
    sK1 = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f48,f92])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f134,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f132,f47])).

fof(f132,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f53,f123])).

fof(f123,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f122,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f122,plain,(
    k3_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f53,f118])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f124,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f55,f119])).

fof(f119,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f49,f105])).

fof(f105,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f48,f93])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f127,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f120,f124])).

fof(f120,plain,(
    k5_xboole_0(sK1,sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f55,f118])).

fof(f636,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f116,f45])).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f109,f47])).

fof(f109,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f68,f93])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f368,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f54,f361])).

fof(f361,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f350,f355])).

fof(f355,plain,(
    sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f48,f248])).

fof(f248,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f247,f106])).

fof(f247,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f53,f232])).

fof(f232,plain,(
    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f229,f93])).

fof(f229,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f53,f106])).

fof(f350,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f349,f248])).

fof(f349,plain,(
    k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f54,f336])).

fof(f336,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f334,f151])).

fof(f151,plain,(
    sK1 = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f133,f150])).

fof(f150,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f143,f44])).

fof(f143,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f52,f135])).

fof(f133,plain,(
    sK1 = k2_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f131,f44])).

fof(f131,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f55,f123])).

fof(f334,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f246,f333])).

fof(f333,plain,(
    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f308,f332])).

fof(f332,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f329,f142])).

fof(f329,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f55,f314])).

fof(f314,plain,(
    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f49,f159])).

fof(f159,plain,(
    k5_xboole_0(sK0,sK1) = k2_xboole_0(k5_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f156,f106])).

fof(f156,plain,(
    k5_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f55,f148])).

fof(f148,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f128,f147])).

fof(f128,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f98,f127])).

fof(f98,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f52,f92])).

fof(f308,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f52,f222])).

fof(f222,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f217,f60])).

fof(f217,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f216,f71])).

fof(f216,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f211,f42])).

fof(f211,plain,
    ( r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f112,f56])).

fof(f112,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f82,f106])).

fof(f246,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK0)) ),
    inference(superposition,[],[f55,f232])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (2059)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (2051)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (2045)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (2043)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (2059)Refutation not found, incomplete strategy% (2059)------------------------------
% 0.22/0.52  % (2059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2059)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2059)Memory used [KB]: 10746
% 0.22/0.52  % (2059)Time elapsed: 0.057 s
% 0.22/0.52  % (2059)------------------------------
% 0.22/0.52  % (2059)------------------------------
% 0.22/0.52  % (2050)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (2048)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (2066)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (2058)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (2039)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (2038)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (2041)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (2037)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (2044)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (2046)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (2062)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (2064)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (2060)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (2061)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (2047)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (2054)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (2040)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (2054)Refutation not found, incomplete strategy% (2054)------------------------------
% 0.22/0.56  % (2054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2054)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2054)Memory used [KB]: 10618
% 0.22/0.56  % (2054)Time elapsed: 0.149 s
% 0.22/0.56  % (2054)------------------------------
% 0.22/0.56  % (2054)------------------------------
% 1.56/0.56  % (2053)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.56  % (2063)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.56  % (2042)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.57  % (2055)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.57  % (2065)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.57  % (2052)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.57  % (2052)Refutation not found, incomplete strategy% (2052)------------------------------
% 1.56/0.57  % (2052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (2052)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (2052)Memory used [KB]: 6140
% 1.56/0.57  % (2052)Time elapsed: 0.003 s
% 1.56/0.57  % (2052)------------------------------
% 1.56/0.57  % (2052)------------------------------
% 1.56/0.57  % (2057)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.58  % (2060)Refutation found. Thanks to Tanya!
% 1.68/0.58  % SZS status Theorem for theBenchmark
% 1.68/0.58  % SZS output start Proof for theBenchmark
% 1.68/0.58  fof(f648,plain,(
% 1.68/0.58    $false),
% 1.68/0.58    inference(subsumption_resolution,[],[f647,f111])).
% 1.68/0.58  fof(f111,plain,(
% 1.68/0.58    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(backward_demodulation,[],[f86,f106])).
% 1.68/0.58  fof(f106,plain,(
% 1.68/0.58    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.68/0.58    inference(superposition,[],[f52,f93])).
% 1.68/0.58  fof(f93,plain,(
% 1.68/0.58    sK1 = k3_xboole_0(sK0,sK1)),
% 1.68/0.58    inference(superposition,[],[f92,f47])).
% 1.68/0.58  fof(f47,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f1])).
% 1.68/0.58  fof(f1,axiom,(
% 1.68/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.68/0.58  fof(f92,plain,(
% 1.68/0.58    sK1 = k3_xboole_0(sK1,sK0)),
% 1.68/0.58    inference(resolution,[],[f87,f60])).
% 1.68/0.58  fof(f60,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f28])).
% 1.68/0.58  fof(f28,plain,(
% 1.68/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.68/0.58    inference(ennf_transformation,[],[f7])).
% 1.68/0.58  fof(f7,axiom,(
% 1.68/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.68/0.58  fof(f87,plain,(
% 1.68/0.58    r1_tarski(sK1,sK0)),
% 1.68/0.58    inference(resolution,[],[f83,f71])).
% 1.68/0.58  fof(f71,plain,(
% 1.68/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.68/0.58    inference(equality_resolution,[],[f63])).
% 1.68/0.58  fof(f63,plain,(
% 1.68/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.68/0.58    inference(cnf_transformation,[],[f39])).
% 1.68/0.58  fof(f39,plain,(
% 1.68/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 1.68/0.58  fof(f38,plain,(
% 1.68/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f37,plain,(
% 1.68/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.68/0.58    inference(rectify,[],[f36])).
% 1.68/0.58  fof(f36,plain,(
% 1.68/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.68/0.58    inference(nnf_transformation,[],[f15])).
% 1.68/0.58  fof(f15,axiom,(
% 1.68/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.68/0.58  fof(f83,plain,(
% 1.68/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(subsumption_resolution,[],[f77,f42])).
% 1.68/0.58  fof(f42,plain,(
% 1.68/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f21])).
% 1.68/0.58  % (2056)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.68/0.58  fof(f21,axiom,(
% 1.68/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.68/0.58  fof(f77,plain,(
% 1.68/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(resolution,[],[f40,f56])).
% 1.68/0.58  fof(f56,plain,(
% 1.68/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f35])).
% 1.68/0.58  fof(f35,plain,(
% 1.68/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.68/0.58    inference(nnf_transformation,[],[f27])).
% 1.68/0.58  fof(f27,plain,(
% 1.68/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f17])).
% 1.68/0.58  fof(f17,axiom,(
% 1.68/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.68/0.58  fof(f40,plain,(
% 1.68/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(cnf_transformation,[],[f34])).
% 1.68/0.58  fof(f34,plain,(
% 1.68/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).
% 1.68/0.58  fof(f33,plain,(
% 1.68/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f26,plain,(
% 1.68/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f24])).
% 1.68/0.58  fof(f24,negated_conjecture,(
% 1.68/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.68/0.58    inference(negated_conjecture,[],[f23])).
% 1.68/0.58  fof(f23,conjecture,(
% 1.68/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.68/0.58  fof(f52,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f4])).
% 1.68/0.58  fof(f4,axiom,(
% 1.68/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.68/0.58  fof(f86,plain,(
% 1.68/0.58    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(subsumption_resolution,[],[f85,f40])).
% 1.68/0.58  fof(f85,plain,(
% 1.68/0.58    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(subsumption_resolution,[],[f84,f82])).
% 1.68/0.58  fof(f82,plain,(
% 1.68/0.58    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(forward_demodulation,[],[f76,f75])).
% 1.68/0.58  fof(f75,plain,(
% 1.68/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.68/0.58    inference(resolution,[],[f40,f62])).
% 1.68/0.58  fof(f62,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f30])).
% 1.68/0.58  fof(f30,plain,(
% 1.68/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f19])).
% 1.68/0.58  fof(f19,axiom,(
% 1.68/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.68/0.58  fof(f76,plain,(
% 1.68/0.58    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(resolution,[],[f40,f61])).
% 1.68/0.58  fof(f61,plain,(
% 1.68/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f29])).
% 1.68/0.58  fof(f29,plain,(
% 1.68/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f20])).
% 1.68/0.58  fof(f20,axiom,(
% 1.68/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.68/0.58  fof(f84,plain,(
% 1.68/0.58    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(superposition,[],[f81,f69])).
% 1.68/0.58  fof(f69,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f32])).
% 1.68/0.58  fof(f32,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.68/0.58    inference(flattening,[],[f31])).
% 1.68/0.58  fof(f31,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.68/0.58    inference(ennf_transformation,[],[f22])).
% 1.68/0.58  fof(f22,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.68/0.58  fof(f81,plain,(
% 1.68/0.58    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(backward_demodulation,[],[f72,f75])).
% 1.68/0.58  fof(f72,plain,(
% 1.68/0.58    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f41,f43])).
% 1.68/0.58  fof(f43,plain,(
% 1.68/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f18])).
% 1.68/0.58  fof(f18,axiom,(
% 1.68/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.68/0.58  fof(f41,plain,(
% 1.68/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.68/0.58    inference(cnf_transformation,[],[f34])).
% 1.68/0.58  fof(f647,plain,(
% 1.68/0.58    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f646,f44])).
% 1.68/0.58  fof(f44,plain,(
% 1.68/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f10])).
% 1.68/0.58  fof(f10,axiom,(
% 1.68/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.68/0.58  fof(f646,plain,(
% 1.68/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.68/0.58    inference(backward_demodulation,[],[f368,f645])).
% 1.68/0.58  fof(f645,plain,(
% 1.68/0.58    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f636,f149])).
% 1.68/0.58  fof(f149,plain,(
% 1.68/0.58    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.68/0.58    inference(backward_demodulation,[],[f127,f147])).
% 1.68/0.58  fof(f147,plain,(
% 1.68/0.58    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.68/0.58    inference(backward_demodulation,[],[f124,f142])).
% 1.68/0.58  fof(f142,plain,(
% 1.68/0.58    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.68/0.58    inference(superposition,[],[f48,f135])).
% 1.68/0.58  fof(f135,plain,(
% 1.68/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 1.68/0.58    inference(forward_demodulation,[],[f134,f118])).
% 1.68/0.58  fof(f118,plain,(
% 1.68/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.68/0.58    inference(superposition,[],[f49,f97])).
% 1.68/0.58  fof(f97,plain,(
% 1.68/0.58    sK1 = k2_xboole_0(sK1,sK1)),
% 1.68/0.58    inference(superposition,[],[f48,f92])).
% 1.68/0.58  fof(f49,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f8])).
% 1.68/0.58  fof(f8,axiom,(
% 1.68/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.68/0.58  fof(f134,plain,(
% 1.68/0.58    k4_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1)),
% 1.68/0.58    inference(forward_demodulation,[],[f132,f47])).
% 1.68/0.58  fof(f132,plain,(
% 1.68/0.58    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0)),
% 1.68/0.58    inference(superposition,[],[f53,f123])).
% 1.68/0.58  fof(f123,plain,(
% 1.68/0.58    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.68/0.58    inference(forward_demodulation,[],[f122,f45])).
% 1.68/0.58  fof(f45,plain,(
% 1.68/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f25])).
% 1.68/0.58  fof(f25,plain,(
% 1.68/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.68/0.58    inference(rectify,[],[f3])).
% 1.68/0.58  fof(f3,axiom,(
% 1.68/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.68/0.58  fof(f122,plain,(
% 1.68/0.58    k3_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.68/0.58    inference(superposition,[],[f53,f118])).
% 1.68/0.58  fof(f53,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f9])).
% 1.68/0.58  fof(f9,axiom,(
% 1.68/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.58  fof(f48,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f6])).
% 1.68/0.58  fof(f6,axiom,(
% 1.68/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.68/0.58  fof(f124,plain,(
% 1.68/0.58    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK0,sK0)),
% 1.68/0.58    inference(superposition,[],[f55,f119])).
% 1.68/0.58  fof(f119,plain,(
% 1.68/0.58    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.68/0.58    inference(superposition,[],[f49,f105])).
% 1.68/0.58  fof(f105,plain,(
% 1.68/0.58    sK0 = k2_xboole_0(sK0,sK1)),
% 1.68/0.58    inference(superposition,[],[f48,f93])).
% 1.68/0.58  fof(f55,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f2])).
% 1.68/0.58  fof(f2,axiom,(
% 1.68/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.68/0.58  fof(f127,plain,(
% 1.68/0.58    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK0,sK0)),
% 1.68/0.58    inference(backward_demodulation,[],[f120,f124])).
% 1.68/0.58  fof(f120,plain,(
% 1.68/0.58    k5_xboole_0(sK1,sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.68/0.58    inference(superposition,[],[f55,f118])).
% 1.68/0.58  fof(f636,plain,(
% 1.68/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f116,f45])).
% 1.68/0.58  fof(f116,plain,(
% 1.68/0.58    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) )),
% 1.68/0.58    inference(forward_demodulation,[],[f109,f47])).
% 1.68/0.58  fof(f109,plain,(
% 1.68/0.58    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 1.68/0.58    inference(superposition,[],[f68,f93])).
% 1.68/0.58  fof(f68,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f5])).
% 1.68/0.58  fof(f5,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.68/0.58  fof(f368,plain,(
% 1.68/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.68/0.58    inference(superposition,[],[f54,f361])).
% 1.68/0.58  fof(f361,plain,(
% 1.68/0.58    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(backward_demodulation,[],[f350,f355])).
% 1.68/0.58  fof(f355,plain,(
% 1.68/0.58    sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f48,f248])).
% 1.68/0.58  fof(f248,plain,(
% 1.68/0.58    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f247,f106])).
% 1.68/0.58  fof(f247,plain,(
% 1.68/0.58    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f53,f232])).
% 1.68/0.58  fof(f232,plain,(
% 1.68/0.58    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f229,f93])).
% 1.68/0.58  fof(f229,plain,(
% 1.68/0.58    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f53,f106])).
% 1.68/0.58  fof(f350,plain,(
% 1.68/0.58    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f349,f248])).
% 1.68/0.58  fof(f349,plain,(
% 1.68/0.58    k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 1.68/0.58    inference(superposition,[],[f54,f336])).
% 1.68/0.58  fof(f336,plain,(
% 1.68/0.58    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f334,f151])).
% 1.68/0.58  fof(f151,plain,(
% 1.68/0.58    sK1 = k2_xboole_0(sK1,k1_xboole_0)),
% 1.68/0.58    inference(backward_demodulation,[],[f133,f150])).
% 1.68/0.58  fof(f150,plain,(
% 1.68/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 1.68/0.58    inference(forward_demodulation,[],[f143,f44])).
% 1.68/0.58  fof(f143,plain,(
% 1.68/0.58    k4_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.68/0.58    inference(superposition,[],[f52,f135])).
% 1.68/0.58  fof(f133,plain,(
% 1.68/0.58    sK1 = k2_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f131,f44])).
% 1.68/0.58  fof(f131,plain,(
% 1.68/0.58    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1))),
% 1.68/0.58    inference(superposition,[],[f55,f123])).
% 1.68/0.58  fof(f334,plain,(
% 1.68/0.58    k2_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(backward_demodulation,[],[f246,f333])).
% 1.68/0.58  fof(f333,plain,(
% 1.68/0.58    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 1.68/0.58    inference(backward_demodulation,[],[f308,f332])).
% 1.68/0.58  fof(f332,plain,(
% 1.68/0.58    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(forward_demodulation,[],[f329,f142])).
% 1.68/0.58  fof(f329,plain,(
% 1.68/0.58    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f55,f314])).
% 1.68/0.58  fof(f314,plain,(
% 1.68/0.58    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f49,f159])).
% 1.68/0.58  fof(f159,plain,(
% 1.68/0.58    k5_xboole_0(sK0,sK1) = k2_xboole_0(k5_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.68/0.58    inference(forward_demodulation,[],[f156,f106])).
% 1.68/0.58  fof(f156,plain,(
% 1.68/0.58    k5_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.68/0.58    inference(superposition,[],[f55,f148])).
% 1.68/0.58  fof(f148,plain,(
% 1.68/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.68/0.58    inference(backward_demodulation,[],[f128,f147])).
% 1.68/0.58  fof(f128,plain,(
% 1.68/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK0)),
% 1.68/0.58    inference(backward_demodulation,[],[f98,f127])).
% 1.68/0.58  fof(f98,plain,(
% 1.68/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 1.68/0.58    inference(superposition,[],[f52,f92])).
% 1.68/0.58  fof(f308,plain,(
% 1.68/0.58    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 1.68/0.58    inference(superposition,[],[f52,f222])).
% 1.68/0.58  fof(f222,plain,(
% 1.68/0.58    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 1.68/0.58    inference(resolution,[],[f217,f60])).
% 1.68/0.58  fof(f217,plain,(
% 1.68/0.58    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 1.68/0.58    inference(resolution,[],[f216,f71])).
% 1.68/0.58  fof(f216,plain,(
% 1.68/0.58    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(subsumption_resolution,[],[f211,f42])).
% 1.68/0.58  fof(f211,plain,(
% 1.68/0.58    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(resolution,[],[f112,f56])).
% 1.68/0.58  fof(f112,plain,(
% 1.68/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.68/0.58    inference(backward_demodulation,[],[f82,f106])).
% 1.68/0.58  fof(f246,plain,(
% 1.68/0.58    k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK0))),
% 1.68/0.58    inference(superposition,[],[f55,f232])).
% 1.68/0.58  fof(f54,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f11])).
% 1.68/0.58  fof(f11,axiom,(
% 1.68/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.68/0.58  % SZS output end Proof for theBenchmark
% 1.68/0.58  % (2060)------------------------------
% 1.68/0.58  % (2060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (2060)Termination reason: Refutation
% 1.68/0.58  
% 1.68/0.58  % (2060)Memory used [KB]: 2046
% 1.68/0.58  % (2060)Time elapsed: 0.153 s
% 1.68/0.58  % (2060)------------------------------
% 1.68/0.58  % (2060)------------------------------
% 1.68/0.58  % (2036)Success in time 0.217 s
%------------------------------------------------------------------------------
