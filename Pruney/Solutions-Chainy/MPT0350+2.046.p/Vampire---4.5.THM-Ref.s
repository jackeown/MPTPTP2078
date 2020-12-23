%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:56 EST 2020

% Result     : Theorem 9.11s
% Output     : Refutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :  155 (5408 expanded)
%              Number of leaves         :   21 (1508 expanded)
%              Depth                    :   37
%              Number of atoms          :  333 (18507 expanded)
%              Number of equality atoms :  127 (4424 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8001,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8000,f5076])).

fof(f5076,plain,(
    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f206,f370])).

fof(f370,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f207,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f207,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f143,f204])).

fof(f204,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f194,f136])).

fof(f136,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f56,f124])).

fof(f124,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f121,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f121,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f108,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f108,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f104,f84])).

fof(f84,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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

fof(f104,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f46,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f194,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f143,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f206,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f88,f204])).

fof(f88,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f47,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8000,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f7999,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f7999,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f7998,f6769])).

fof(f6769,plain,(
    ! [X13] : k1_xboole_0 = k4_xboole_0(X13,X13) ),
    inference(backward_demodulation,[],[f3662,f485])).

fof(f485,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = X4 ),
    inference(forward_demodulation,[],[f484,f89])).

fof(f89,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f53,f51])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f484,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f478,f51])).

fof(f478,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(superposition,[],[f57,f120])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f49,f62])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f3662,plain,(
    ! [X13] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X13,X13) ),
    inference(superposition,[],[f2800,f89])).

fof(f2800,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X10) = k5_xboole_0(X10,k4_xboole_0(X11,X11)) ),
    inference(superposition,[],[f1019,f2688])).

fof(f2688,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f2624,f2624])).

fof(f2624,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2607,f421])).

fof(f421,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK3(X0,X0,X1),X1)
      | r2_hidden(sK3(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2607,plain,(
    ! [X2] : ~ r2_hidden(X2,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2604,f1285])).

fof(f1285,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)))
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f87,f734])).

fof(f734,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f56,f714])).

fof(f714,plain,(
    k2_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f705,f363])).

fof(f363,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f330,f352])).

fof(f352,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f189,f182])).

fof(f182,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f57,f124])).

fof(f189,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f181,f53])).

fof(f181,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f57,f121])).

fof(f330,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f189,f53])).

fof(f705,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f306,f216])).

fof(f216,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f210,f62])).

fof(f210,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f153,f204])).

fof(f153,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f149,f84])).

fof(f149,plain,(
    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f143,f58])).

fof(f306,plain,(
    ! [X6] : k5_xboole_0(sK1,k3_xboole_0(X6,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X6)) ),
    inference(forward_demodulation,[],[f292,f52])).

fof(f292,plain,(
    ! [X6] : k3_xboole_0(k5_xboole_0(sK1,X6),sK0) = k5_xboole_0(sK1,k3_xboole_0(X6,sK0)) ),
    inference(superposition,[],[f71,f121])).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2604,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f86,f2540])).

fof(f2540,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2539,f362])).

fof(f362,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f329,f352])).

fof(f329,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f189,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2539,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f2486,f241])).

fof(f241,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X7,k5_xboole_0(X8,X9)) ),
    inference(superposition,[],[f70,f53])).

fof(f2486,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f243,f216])).

fof(f243,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,k3_xboole_0(k5_xboole_0(X13,X14),X15))) ),
    inference(superposition,[],[f70,f56])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1019,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f239,f133])).

fof(f133,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f56,f52])).

fof(f239,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f70,f57])).

fof(f7998,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f7997,f837])).

fof(f837,plain,(
    ! [X7] : k3_xboole_0(sK1,k5_xboole_0(sK0,X7)) = k4_xboole_0(sK1,X7) ),
    inference(forward_demodulation,[],[f307,f133])).

fof(f307,plain,(
    ! [X7] : k5_xboole_0(sK1,k3_xboole_0(X7,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X7)) ),
    inference(forward_demodulation,[],[f293,f52])).

fof(f293,plain,(
    ! [X7] : k3_xboole_0(k5_xboole_0(sK0,X7),sK1) = k5_xboole_0(sK1,k3_xboole_0(X7,sK1)) ),
    inference(superposition,[],[f71,f124])).

fof(f7997,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f7897,f124])).

fof(f7897,plain,(
    k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f7727,f7544])).

fof(f7544,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f7521,f51])).

fof(f7521,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f362,f7494])).

fof(f7494,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f7466,f6783])).

fof(f6783,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f421,f6769])).

fof(f7466,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f7456,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f87,f135])).

fof(f135,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f56,f121])).

fof(f7456,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k5_xboole_0(sK1,sK1)) ) ),
    inference(resolution,[],[f7398,f746])).

fof(f746,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(X2,k5_xboole_0(sK1,sK1)) ) ),
    inference(superposition,[],[f86,f727])).

fof(f727,plain,(
    k2_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f720,f362])).

fof(f720,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f56,f707])).

fof(f707,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f306,f121])).

fof(f7398,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f7381,f6788])).

fof(f6788,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f2717,f6769])).

fof(f2717,plain,(
    ! [X4,X3] : ~ r2_hidden(X4,k4_xboole_0(X3,X3)) ),
    inference(superposition,[],[f2607,f2624])).

fof(f7381,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f85,f6859])).

fof(f6859,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f6789,f120])).

fof(f6789,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f2719,f6769])).

fof(f2719,plain,(
    ! [X7] : k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k3_xboole_0(k4_xboole_0(X7,X7),sK1) ),
    inference(superposition,[],[f1645,f2624])).

fof(f1645,plain,(
    ! [X13] : k3_xboole_0(k5_xboole_0(sK0,X13),sK1) = k4_xboole_0(sK1,X13) ),
    inference(forward_demodulation,[],[f1606,f133])).

fof(f1606,plain,(
    ! [X13] : k3_xboole_0(k5_xboole_0(sK0,X13),sK1) = k5_xboole_0(sK1,k3_xboole_0(X13,sK1)) ),
    inference(superposition,[],[f290,f121])).

fof(f290,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f71,f52])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7727,plain,(
    ! [X8,X9] : k5_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9))) = k2_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f188,f658])).

fof(f658,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f179,f174])).

fof(f174,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f57,f53])).

fof(f179,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f57,f52])).

fof(f188,plain,(
    ! [X8,X9] : k2_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f178,f52])).

fof(f178,plain,(
    ! [X8,X9] : k2_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9))) ),
    inference(superposition,[],[f57,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (14527)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (14513)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (14512)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (14519)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (14518)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (14532)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (14520)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14534)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (14514)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (14535)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (14534)Refutation not found, incomplete strategy% (14534)------------------------------
% 0.21/0.53  % (14534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14534)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14534)Memory used [KB]: 10746
% 0.21/0.53  % (14534)Time elapsed: 0.117 s
% 0.21/0.53  % (14534)------------------------------
% 0.21/0.53  % (14534)------------------------------
% 0.21/0.53  % (14516)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (14517)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (14515)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (14536)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (14523)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (14541)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (14537)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (14528)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (14525)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (14530)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (14531)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (14521)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (14538)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (14529)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (14533)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (14529)Refutation not found, incomplete strategy% (14529)------------------------------
% 0.21/0.54  % (14529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14529)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14529)Memory used [KB]: 10618
% 0.21/0.54  % (14529)Time elapsed: 0.147 s
% 0.21/0.54  % (14529)------------------------------
% 0.21/0.54  % (14529)------------------------------
% 0.21/0.54  % (14539)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (14540)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (14522)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (14526)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (14524)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.13/0.70  % (14548)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.69/0.71  % (14547)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.15/0.81  % (14517)Time limit reached!
% 3.15/0.81  % (14517)------------------------------
% 3.15/0.81  % (14517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.81  % (14517)Termination reason: Time limit
% 3.15/0.81  
% 3.15/0.81  % (14517)Memory used [KB]: 9338
% 3.15/0.81  % (14517)Time elapsed: 0.416 s
% 3.15/0.81  % (14517)------------------------------
% 3.15/0.81  % (14517)------------------------------
% 4.17/0.90  % (14524)Time limit reached!
% 4.17/0.90  % (14524)------------------------------
% 4.17/0.90  % (14524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.90  % (14524)Termination reason: Time limit
% 4.17/0.90  % (14524)Termination phase: Saturation
% 4.17/0.90  
% 4.17/0.90  % (14524)Memory used [KB]: 9083
% 4.17/0.90  % (14524)Time elapsed: 0.500 s
% 4.17/0.90  % (14524)------------------------------
% 4.17/0.90  % (14524)------------------------------
% 4.17/0.90  % (14522)Time limit reached!
% 4.17/0.90  % (14522)------------------------------
% 4.17/0.90  % (14522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.90  % (14522)Termination reason: Time limit
% 4.17/0.90  
% 4.17/0.90  % (14522)Memory used [KB]: 12409
% 4.17/0.90  % (14522)Time elapsed: 0.509 s
% 4.17/0.90  % (14522)------------------------------
% 4.17/0.90  % (14522)------------------------------
% 4.17/0.91  % (14512)Time limit reached!
% 4.17/0.91  % (14512)------------------------------
% 4.17/0.91  % (14512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.91  % (14512)Termination reason: Time limit
% 4.17/0.91  
% 4.17/0.91  % (14512)Memory used [KB]: 5628
% 4.17/0.91  % (14512)Time elapsed: 0.503 s
% 4.17/0.91  % (14512)------------------------------
% 4.17/0.91  % (14512)------------------------------
% 4.43/0.98  % (14556)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.43/0.99  % (14513)Time limit reached!
% 4.43/0.99  % (14513)------------------------------
% 4.43/0.99  % (14513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.99  % (14513)Termination reason: Time limit
% 4.43/0.99  % (14513)Termination phase: Saturation
% 4.43/0.99  
% 4.43/0.99  % (14513)Memory used [KB]: 11001
% 4.43/0.99  % (14513)Time elapsed: 0.500 s
% 4.43/0.99  % (14513)------------------------------
% 4.43/0.99  % (14513)------------------------------
% 4.94/1.01  % (14528)Time limit reached!
% 4.94/1.01  % (14528)------------------------------
% 4.94/1.01  % (14528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.01  % (14528)Termination reason: Time limit
% 4.94/1.01  
% 4.94/1.01  % (14528)Memory used [KB]: 16502
% 4.94/1.01  % (14528)Time elapsed: 0.608 s
% 4.94/1.01  % (14528)------------------------------
% 4.94/1.01  % (14528)------------------------------
% 4.94/1.02  % (14540)Time limit reached!
% 4.94/1.02  % (14540)------------------------------
% 4.94/1.02  % (14540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.02  % (14540)Termination reason: Time limit
% 4.94/1.02  % (14540)Termination phase: Saturation
% 4.94/1.02  
% 4.94/1.02  % (14540)Memory used [KB]: 9594
% 4.94/1.02  % (14540)Time elapsed: 0.629 s
% 4.94/1.02  % (14540)------------------------------
% 4.94/1.02  % (14540)------------------------------
% 4.94/1.03  % (14558)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.94/1.05  % (14519)Time limit reached!
% 4.94/1.05  % (14519)------------------------------
% 4.94/1.05  % (14519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.05  % (14519)Termination reason: Time limit
% 4.94/1.05  
% 4.94/1.05  % (14519)Memory used [KB]: 10874
% 4.94/1.05  % (14519)Time elapsed: 0.615 s
% 4.94/1.05  % (14519)------------------------------
% 4.94/1.05  % (14519)------------------------------
% 4.94/1.05  % (14559)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.94/1.05  % (14557)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.65/1.10  % (14560)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.65/1.15  % (14562)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.65/1.17  % (14561)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.42/1.18  % (14563)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.65/1.23  % (14533)Time limit reached!
% 6.65/1.23  % (14533)------------------------------
% 6.65/1.23  % (14533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.65/1.23  % (14533)Termination reason: Time limit
% 6.65/1.23  % (14533)Termination phase: Saturation
% 6.65/1.23  
% 6.65/1.23  % (14533)Memory used [KB]: 10362
% 6.65/1.23  % (14533)Time elapsed: 0.800 s
% 6.65/1.23  % (14533)------------------------------
% 6.65/1.23  % (14533)------------------------------
% 7.56/1.33  % (14558)Time limit reached!
% 7.56/1.33  % (14558)------------------------------
% 7.56/1.33  % (14558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.56/1.33  % (14558)Termination reason: Time limit
% 7.56/1.33  
% 7.56/1.33  % (14558)Memory used [KB]: 14328
% 7.56/1.33  % (14558)Time elapsed: 0.401 s
% 7.56/1.33  % (14558)------------------------------
% 7.56/1.33  % (14558)------------------------------
% 7.56/1.35  % (14557)Time limit reached!
% 7.56/1.35  % (14557)------------------------------
% 7.56/1.35  % (14557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.56/1.35  % (14557)Termination reason: Time limit
% 7.56/1.35  
% 7.56/1.35  % (14557)Memory used [KB]: 7164
% 7.56/1.35  % (14557)Time elapsed: 0.424 s
% 7.56/1.35  % (14557)------------------------------
% 7.56/1.35  % (14557)------------------------------
% 7.56/1.35  % (14564)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.10/1.40  % (14514)Time limit reached!
% 8.10/1.40  % (14514)------------------------------
% 8.10/1.40  % (14514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.10/1.40  % (14514)Termination reason: Time limit
% 8.10/1.40  
% 8.10/1.40  % (14514)Memory used [KB]: 17654
% 8.10/1.40  % (14514)Time elapsed: 1.005 s
% 8.10/1.40  % (14514)------------------------------
% 8.10/1.40  % (14514)------------------------------
% 8.10/1.46  % (14565)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.71/1.49  % (14566)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.11/1.53  % (14560)Refutation found. Thanks to Tanya!
% 9.11/1.53  % SZS status Theorem for theBenchmark
% 9.11/1.53  % SZS output start Proof for theBenchmark
% 9.11/1.53  fof(f8001,plain,(
% 9.11/1.53    $false),
% 9.11/1.53    inference(subsumption_resolution,[],[f8000,f5076])).
% 9.11/1.53  fof(f5076,plain,(
% 9.11/1.53    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 9.11/1.53    inference(superposition,[],[f206,f370])).
% 9.11/1.53  fof(f370,plain,(
% 9.11/1.53    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 9.11/1.53    inference(unit_resulting_resolution,[],[f46,f207,f72])).
% 9.11/1.53  fof(f72,plain,(
% 9.11/1.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 9.11/1.53    inference(cnf_transformation,[],[f33])).
% 9.11/1.53  fof(f33,plain,(
% 9.11/1.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.11/1.53    inference(flattening,[],[f32])).
% 9.11/1.54  fof(f32,plain,(
% 9.11/1.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 9.11/1.54    inference(ennf_transformation,[],[f24])).
% 9.11/1.54  fof(f24,axiom,(
% 9.11/1.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 9.11/1.54  fof(f207,plain,(
% 9.11/1.54    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 9.11/1.54    inference(backward_demodulation,[],[f143,f204])).
% 9.11/1.54  fof(f204,plain,(
% 9.11/1.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 9.11/1.54    inference(forward_demodulation,[],[f194,f136])).
% 9.11/1.54  fof(f136,plain,(
% 9.11/1.54    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 9.11/1.54    inference(superposition,[],[f56,f124])).
% 9.11/1.54  fof(f124,plain,(
% 9.11/1.54    sK1 = k3_xboole_0(sK0,sK1)),
% 9.11/1.54    inference(superposition,[],[f121,f52])).
% 9.11/1.54  fof(f52,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f1])).
% 9.11/1.54  fof(f1,axiom,(
% 9.11/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.11/1.54  fof(f121,plain,(
% 9.11/1.54    sK1 = k3_xboole_0(sK1,sK0)),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f108,f62])).
% 9.11/1.54  fof(f62,plain,(
% 9.11/1.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 9.11/1.54    inference(cnf_transformation,[],[f29])).
% 9.11/1.54  fof(f29,plain,(
% 9.11/1.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 9.11/1.54    inference(ennf_transformation,[],[f6])).
% 9.11/1.54  fof(f6,axiom,(
% 9.11/1.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 9.11/1.54  fof(f108,plain,(
% 9.11/1.54    r1_tarski(sK1,sK0)),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f104,f84])).
% 9.11/1.54  fof(f84,plain,(
% 9.11/1.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 9.11/1.54    inference(equality_resolution,[],[f65])).
% 9.11/1.54  fof(f65,plain,(
% 9.11/1.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 9.11/1.54    inference(cnf_transformation,[],[f40])).
% 9.11/1.54  fof(f40,plain,(
% 9.11/1.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 9.11/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 9.11/1.54  fof(f39,plain,(
% 9.11/1.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 9.11/1.54    introduced(choice_axiom,[])).
% 9.11/1.54  fof(f38,plain,(
% 9.11/1.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 9.11/1.54    inference(rectify,[],[f37])).
% 9.11/1.54  fof(f37,plain,(
% 9.11/1.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 9.11/1.54    inference(nnf_transformation,[],[f17])).
% 9.11/1.54  fof(f17,axiom,(
% 9.11/1.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 9.11/1.54  fof(f104,plain,(
% 9.11/1.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f48,f46,f58])).
% 9.11/1.54  fof(f58,plain,(
% 9.11/1.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f36])).
% 9.11/1.54  fof(f36,plain,(
% 9.11/1.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 9.11/1.54    inference(nnf_transformation,[],[f28])).
% 9.11/1.54  fof(f28,plain,(
% 9.11/1.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 9.11/1.54    inference(ennf_transformation,[],[f19])).
% 9.11/1.54  fof(f19,axiom,(
% 9.11/1.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 9.11/1.54  fof(f48,plain,(
% 9.11/1.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 9.11/1.54    inference(cnf_transformation,[],[f23])).
% 9.11/1.54  fof(f23,axiom,(
% 9.11/1.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 9.11/1.54  fof(f56,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.11/1.54    inference(cnf_transformation,[],[f4])).
% 9.11/1.54  fof(f4,axiom,(
% 9.11/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 9.11/1.54  fof(f194,plain,(
% 9.11/1.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f46,f64])).
% 9.11/1.54  fof(f64,plain,(
% 9.11/1.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f31])).
% 9.11/1.54  fof(f31,plain,(
% 9.11/1.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.11/1.54    inference(ennf_transformation,[],[f21])).
% 9.11/1.54  fof(f21,axiom,(
% 9.11/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 9.11/1.54  fof(f143,plain,(
% 9.11/1.54    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f46,f63])).
% 9.11/1.54  fof(f63,plain,(
% 9.11/1.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 9.11/1.54    inference(cnf_transformation,[],[f30])).
% 9.11/1.54  fof(f30,plain,(
% 9.11/1.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.11/1.54    inference(ennf_transformation,[],[f22])).
% 9.11/1.54  fof(f22,axiom,(
% 9.11/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 9.11/1.54  fof(f46,plain,(
% 9.11/1.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 9.11/1.54    inference(cnf_transformation,[],[f35])).
% 9.11/1.54  fof(f35,plain,(
% 9.11/1.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 9.11/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).
% 9.11/1.54  fof(f34,plain,(
% 9.11/1.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 9.11/1.54    introduced(choice_axiom,[])).
% 9.11/1.54  fof(f27,plain,(
% 9.11/1.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.11/1.54    inference(ennf_transformation,[],[f26])).
% 9.11/1.54  fof(f26,negated_conjecture,(
% 9.11/1.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 9.11/1.54    inference(negated_conjecture,[],[f25])).
% 9.11/1.54  fof(f25,conjecture,(
% 9.11/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 9.11/1.54  fof(f206,plain,(
% 9.11/1.54    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(backward_demodulation,[],[f88,f204])).
% 9.11/1.54  fof(f88,plain,(
% 9.11/1.54    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 9.11/1.54    inference(backward_demodulation,[],[f47,f50])).
% 9.11/1.54  fof(f50,plain,(
% 9.11/1.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 9.11/1.54    inference(cnf_transformation,[],[f20])).
% 9.11/1.54  fof(f20,axiom,(
% 9.11/1.54    ! [X0] : k2_subset_1(X0) = X0),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 9.11/1.54  fof(f47,plain,(
% 9.11/1.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 9.11/1.54    inference(cnf_transformation,[],[f35])).
% 9.11/1.54  fof(f8000,plain,(
% 9.11/1.54    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f7999,f51])).
% 9.11/1.54  fof(f51,plain,(
% 9.11/1.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.11/1.54    inference(cnf_transformation,[],[f8])).
% 9.11/1.54  fof(f8,axiom,(
% 9.11/1.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 9.11/1.54  fof(f7999,plain,(
% 9.11/1.54    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 9.11/1.54    inference(forward_demodulation,[],[f7998,f6769])).
% 9.11/1.54  fof(f6769,plain,(
% 9.11/1.54    ( ! [X13] : (k1_xboole_0 = k4_xboole_0(X13,X13)) )),
% 9.11/1.54    inference(backward_demodulation,[],[f3662,f485])).
% 9.11/1.54  fof(f485,plain,(
% 9.11/1.54    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = X4) )),
% 9.11/1.54    inference(forward_demodulation,[],[f484,f89])).
% 9.11/1.54  fof(f89,plain,(
% 9.11/1.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 9.11/1.54    inference(superposition,[],[f53,f51])).
% 9.11/1.54  fof(f53,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f2])).
% 9.11/1.54  fof(f2,axiom,(
% 9.11/1.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 9.11/1.54  fof(f484,plain,(
% 9.11/1.54    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,X4)) )),
% 9.11/1.54    inference(forward_demodulation,[],[f478,f51])).
% 9.11/1.54  fof(f478,plain,(
% 9.11/1.54    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 9.11/1.54    inference(superposition,[],[f57,f120])).
% 9.11/1.54  fof(f120,plain,(
% 9.11/1.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f49,f62])).
% 9.11/1.54  fof(f49,plain,(
% 9.11/1.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f7])).
% 9.11/1.54  fof(f7,axiom,(
% 9.11/1.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 9.11/1.54  fof(f57,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 9.11/1.54    inference(cnf_transformation,[],[f10])).
% 9.11/1.54  fof(f10,axiom,(
% 9.11/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 9.11/1.54  fof(f3662,plain,(
% 9.11/1.54    ( ! [X13] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X13,X13)) )),
% 9.11/1.54    inference(superposition,[],[f2800,f89])).
% 9.11/1.54  fof(f2800,plain,(
% 9.11/1.54    ( ! [X10,X11] : (k2_xboole_0(X10,X10) = k5_xboole_0(X10,k4_xboole_0(X11,X11))) )),
% 9.11/1.54    inference(superposition,[],[f1019,f2688])).
% 9.11/1.54  fof(f2688,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1)) )),
% 9.11/1.54    inference(superposition,[],[f2624,f2624])).
% 9.11/1.54  fof(f2624,plain,(
% 9.11/1.54    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))) )),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f2607,f421])).
% 9.11/1.54  fof(f421,plain,(
% 9.11/1.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 9.11/1.54    inference(duplicate_literal_removal,[],[f417])).
% 9.11/1.54  fof(f417,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = X1 | r2_hidden(sK3(X0,X0,X1),X1) | r2_hidden(sK3(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 9.11/1.54    inference(resolution,[],[f77,f76])).
% 9.11/1.54  fof(f76,plain,(
% 9.11/1.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 9.11/1.54    inference(cnf_transformation,[],[f45])).
% 9.11/1.54  fof(f45,plain,(
% 9.11/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.11/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 9.11/1.54  fof(f44,plain,(
% 9.11/1.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 9.11/1.54    introduced(choice_axiom,[])).
% 9.11/1.54  fof(f43,plain,(
% 9.11/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.11/1.54    inference(rectify,[],[f42])).
% 9.11/1.54  fof(f42,plain,(
% 9.11/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.11/1.54    inference(flattening,[],[f41])).
% 9.11/1.54  fof(f41,plain,(
% 9.11/1.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.11/1.54    inference(nnf_transformation,[],[f3])).
% 9.11/1.54  fof(f3,axiom,(
% 9.11/1.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 9.11/1.54  fof(f77,plain,(
% 9.11/1.54    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f45])).
% 9.11/1.54  fof(f2607,plain,(
% 9.11/1.54    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)))) )),
% 9.11/1.54    inference(subsumption_resolution,[],[f2604,f1285])).
% 9.11/1.54  fof(f1285,plain,(
% 9.11/1.54    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))) | r2_hidden(X1,sK0)) )),
% 9.11/1.54    inference(superposition,[],[f87,f734])).
% 9.11/1.54  fof(f734,plain,(
% 9.11/1.54    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(superposition,[],[f56,f714])).
% 9.11/1.54  fof(f714,plain,(
% 9.11/1.54    k2_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f705,f363])).
% 9.11/1.54  fof(f363,plain,(
% 9.11/1.54    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f330,f352])).
% 9.11/1.54  fof(f352,plain,(
% 9.11/1.54    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1)),
% 9.11/1.54    inference(backward_demodulation,[],[f189,f182])).
% 9.11/1.54  fof(f182,plain,(
% 9.11/1.54    k2_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 9.11/1.54    inference(superposition,[],[f57,f124])).
% 9.11/1.54  fof(f189,plain,(
% 9.11/1.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 9.11/1.54    inference(forward_demodulation,[],[f181,f53])).
% 9.11/1.54  fof(f181,plain,(
% 9.11/1.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 9.11/1.54    inference(superposition,[],[f57,f121])).
% 9.11/1.54  fof(f330,plain,(
% 9.11/1.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(superposition,[],[f189,f53])).
% 9.11/1.54  fof(f705,plain,(
% 9.11/1.54    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 9.11/1.54    inference(superposition,[],[f306,f216])).
% 9.11/1.54  fof(f216,plain,(
% 9.11/1.54    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f210,f62])).
% 9.11/1.54  fof(f210,plain,(
% 9.11/1.54    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 9.11/1.54    inference(backward_demodulation,[],[f153,f204])).
% 9.11/1.54  fof(f153,plain,(
% 9.11/1.54    r1_tarski(k3_subset_1(sK0,sK1),sK0)),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f149,f84])).
% 9.11/1.54  fof(f149,plain,(
% 9.11/1.54    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f48,f143,f58])).
% 9.11/1.54  fof(f306,plain,(
% 9.11/1.54    ( ! [X6] : (k5_xboole_0(sK1,k3_xboole_0(X6,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X6))) )),
% 9.11/1.54    inference(forward_demodulation,[],[f292,f52])).
% 9.11/1.54  fof(f292,plain,(
% 9.11/1.54    ( ! [X6] : (k3_xboole_0(k5_xboole_0(sK1,X6),sK0) = k5_xboole_0(sK1,k3_xboole_0(X6,sK0))) )),
% 9.11/1.54    inference(superposition,[],[f71,f121])).
% 9.11/1.54  fof(f71,plain,(
% 9.11/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 9.11/1.54    inference(cnf_transformation,[],[f5])).
% 9.11/1.54  fof(f5,axiom,(
% 9.11/1.54    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 9.11/1.54  fof(f87,plain,(
% 9.11/1.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 9.11/1.54    inference(equality_resolution,[],[f73])).
% 9.11/1.54  fof(f73,plain,(
% 9.11/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 9.11/1.54    inference(cnf_transformation,[],[f45])).
% 9.11/1.54  fof(f2604,plain,(
% 9.11/1.54    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))) | ~r2_hidden(X2,sK0)) )),
% 9.11/1.54    inference(superposition,[],[f86,f2540])).
% 9.11/1.54  fof(f2540,plain,(
% 9.11/1.54    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f2539,f362])).
% 9.11/1.54  fof(f362,plain,(
% 9.11/1.54    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f329,f352])).
% 9.11/1.54  fof(f329,plain,(
% 9.11/1.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 9.11/1.54    inference(superposition,[],[f189,f70])).
% 9.11/1.54  fof(f70,plain,(
% 9.11/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 9.11/1.54    inference(cnf_transformation,[],[f9])).
% 9.11/1.54  fof(f9,axiom,(
% 9.11/1.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 9.11/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 9.11/1.54  fof(f2539,plain,(
% 9.11/1.54    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 9.11/1.54    inference(forward_demodulation,[],[f2486,f241])).
% 9.11/1.54  fof(f241,plain,(
% 9.11/1.54    ( ! [X8,X7,X9] : (k5_xboole_0(X9,k5_xboole_0(X7,X8)) = k5_xboole_0(X7,k5_xboole_0(X8,X9))) )),
% 9.11/1.54    inference(superposition,[],[f70,f53])).
% 9.11/1.54  fof(f2486,plain,(
% 9.11/1.54    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 9.11/1.54    inference(superposition,[],[f243,f216])).
% 9.11/1.54  fof(f243,plain,(
% 9.11/1.54    ( ! [X14,X15,X13] : (k4_xboole_0(k5_xboole_0(X13,X14),X15) = k5_xboole_0(X13,k5_xboole_0(X14,k3_xboole_0(k5_xboole_0(X13,X14),X15)))) )),
% 9.11/1.54    inference(superposition,[],[f70,f56])).
% 9.11/1.54  fof(f86,plain,(
% 9.11/1.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 9.11/1.54    inference(equality_resolution,[],[f74])).
% 9.11/1.54  fof(f74,plain,(
% 9.11/1.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 9.11/1.54    inference(cnf_transformation,[],[f45])).
% 9.11/1.54  fof(f1019,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.11/1.54    inference(forward_demodulation,[],[f239,f133])).
% 9.11/1.54  fof(f133,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 9.11/1.54    inference(superposition,[],[f56,f52])).
% 9.11/1.54  fof(f239,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 9.11/1.54    inference(superposition,[],[f70,f57])).
% 9.11/1.54  fof(f7998,plain,(
% 9.11/1.54    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f7997,f837])).
% 9.11/1.54  fof(f837,plain,(
% 9.11/1.54    ( ! [X7] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X7)) = k4_xboole_0(sK1,X7)) )),
% 9.11/1.54    inference(forward_demodulation,[],[f307,f133])).
% 9.11/1.54  fof(f307,plain,(
% 9.11/1.54    ( ! [X7] : (k5_xboole_0(sK1,k3_xboole_0(X7,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X7))) )),
% 9.11/1.54    inference(forward_demodulation,[],[f293,f52])).
% 9.11/1.54  fof(f293,plain,(
% 9.11/1.54    ( ! [X7] : (k3_xboole_0(k5_xboole_0(sK0,X7),sK1) = k5_xboole_0(sK1,k3_xboole_0(X7,sK1))) )),
% 9.11/1.54    inference(superposition,[],[f71,f124])).
% 9.11/1.54  fof(f7997,plain,(
% 9.11/1.54    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 9.11/1.54    inference(forward_demodulation,[],[f7897,f124])).
% 9.11/1.54  fof(f7897,plain,(
% 9.11/1.54    k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(superposition,[],[f7727,f7544])).
% 9.11/1.54  fof(f7544,plain,(
% 9.11/1.54    sK0 = k2_xboole_0(sK0,sK1)),
% 9.11/1.54    inference(forward_demodulation,[],[f7521,f51])).
% 9.11/1.54  fof(f7521,plain,(
% 9.11/1.54    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 9.11/1.54    inference(backward_demodulation,[],[f362,f7494])).
% 9.11/1.54  fof(f7494,plain,(
% 9.11/1.54    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 9.11/1.54    inference(unit_resulting_resolution,[],[f7466,f6783])).
% 9.11/1.54  fof(f6783,plain,(
% 9.11/1.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 9.11/1.54    inference(backward_demodulation,[],[f421,f6769])).
% 9.11/1.54  fof(f7466,plain,(
% 9.11/1.54    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1))) )),
% 9.11/1.54    inference(subsumption_resolution,[],[f7456,f139])).
% 9.11/1.54  fof(f139,plain,(
% 9.11/1.54    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1)) | r2_hidden(X0,sK1)) )),
% 9.11/1.54    inference(superposition,[],[f87,f135])).
% 9.11/1.54  fof(f135,plain,(
% 9.11/1.54    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 9.11/1.54    inference(superposition,[],[f56,f121])).
% 9.11/1.54  fof(f7456,plain,(
% 9.11/1.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k5_xboole_0(sK1,sK1))) )),
% 9.11/1.54    inference(resolution,[],[f7398,f746])).
% 9.11/1.54  fof(f746,plain,(
% 9.11/1.54    ( ! [X2] : (~r2_hidden(X2,k2_xboole_0(sK0,sK1)) | ~r2_hidden(X2,k5_xboole_0(sK1,sK1))) )),
% 9.11/1.54    inference(superposition,[],[f86,f727])).
% 9.11/1.54  fof(f727,plain,(
% 9.11/1.54    k2_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f720,f362])).
% 9.11/1.54  fof(f720,plain,(
% 9.11/1.54    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 9.11/1.54    inference(superposition,[],[f56,f707])).
% 9.11/1.54  fof(f707,plain,(
% 9.11/1.54    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 9.11/1.54    inference(superposition,[],[f306,f121])).
% 9.11/1.54  fof(f7398,plain,(
% 9.11/1.54    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 9.11/1.54    inference(subsumption_resolution,[],[f7381,f6788])).
% 9.11/1.54  fof(f6788,plain,(
% 9.11/1.54    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 9.11/1.54    inference(backward_demodulation,[],[f2717,f6769])).
% 9.11/1.54  fof(f2717,plain,(
% 9.11/1.54    ( ! [X4,X3] : (~r2_hidden(X4,k4_xboole_0(X3,X3))) )),
% 9.11/1.54    inference(superposition,[],[f2607,f2624])).
% 9.11/1.54  fof(f7381,plain,(
% 9.11/1.54    ( ! [X1] : (r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,k2_xboole_0(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 9.11/1.54    inference(superposition,[],[f85,f6859])).
% 9.11/1.54  fof(f6859,plain,(
% 9.11/1.54    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(forward_demodulation,[],[f6789,f120])).
% 9.11/1.54  fof(f6789,plain,(
% 9.11/1.54    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 9.11/1.54    inference(backward_demodulation,[],[f2719,f6769])).
% 9.11/1.54  fof(f2719,plain,(
% 9.11/1.54    ( ! [X7] : (k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k3_xboole_0(k4_xboole_0(X7,X7),sK1)) )),
% 9.11/1.54    inference(superposition,[],[f1645,f2624])).
% 9.11/1.54  fof(f1645,plain,(
% 9.11/1.54    ( ! [X13] : (k3_xboole_0(k5_xboole_0(sK0,X13),sK1) = k4_xboole_0(sK1,X13)) )),
% 9.11/1.54    inference(forward_demodulation,[],[f1606,f133])).
% 9.11/1.54  fof(f1606,plain,(
% 9.11/1.54    ( ! [X13] : (k3_xboole_0(k5_xboole_0(sK0,X13),sK1) = k5_xboole_0(sK1,k3_xboole_0(X13,sK1))) )),
% 9.11/1.54    inference(superposition,[],[f290,f121])).
% 9.11/1.54  fof(f290,plain,(
% 9.11/1.54    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1))) )),
% 9.11/1.54    inference(superposition,[],[f71,f52])).
% 9.11/1.54  fof(f85,plain,(
% 9.11/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 9.11/1.54    inference(equality_resolution,[],[f75])).
% 9.11/1.54  fof(f75,plain,(
% 9.11/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 9.11/1.54    inference(cnf_transformation,[],[f45])).
% 9.11/1.54  fof(f7727,plain,(
% 9.11/1.54    ( ! [X8,X9] : (k5_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9))) = k2_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9))) )),
% 9.11/1.54    inference(backward_demodulation,[],[f188,f658])).
% 9.11/1.54  fof(f658,plain,(
% 9.11/1.54    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3)) )),
% 9.11/1.54    inference(superposition,[],[f179,f174])).
% 9.11/1.54  fof(f174,plain,(
% 9.11/1.54    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2))) )),
% 9.11/1.54    inference(superposition,[],[f57,f53])).
% 9.11/1.54  fof(f179,plain,(
% 9.11/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 9.11/1.54    inference(superposition,[],[f57,f52])).
% 9.11/1.54  fof(f188,plain,(
% 9.11/1.54    ( ! [X8,X9] : (k2_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)))) )),
% 9.11/1.54    inference(forward_demodulation,[],[f178,f52])).
% 9.11/1.54  fof(f178,plain,(
% 9.11/1.54    ( ! [X8,X9] : (k2_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X8,X9)))) )),
% 9.11/1.54    inference(superposition,[],[f57,f57])).
% 9.11/1.54  % SZS output end Proof for theBenchmark
% 9.11/1.54  % (14560)------------------------------
% 9.11/1.54  % (14560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.11/1.54  % (14560)Termination reason: Refutation
% 9.11/1.54  
% 9.11/1.54  % (14560)Memory used [KB]: 7675
% 9.11/1.54  % (14560)Time elapsed: 0.530 s
% 9.11/1.54  % (14560)------------------------------
% 9.11/1.54  % (14560)------------------------------
% 9.11/1.55  % (14511)Success in time 1.18 s
%------------------------------------------------------------------------------
