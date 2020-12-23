%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:38 EST 2020

% Result     : Theorem 11.02s
% Output     : Refutation 11.02s
% Verified   : 
% Statistics : Number of formulae       :  249 (10959 expanded)
%              Number of leaves         :   28 (2909 expanded)
%              Depth                    :   39
%              Number of atoms          :  602 (53572 expanded)
%              Number of equality atoms :  205 (13877 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3763,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3688,f3709])).

fof(f3709,plain,(
    ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f3708,f3297])).

fof(f3297,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f238,f3296])).

fof(f3296,plain,(
    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3284,f102])).

fof(f102,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f3284,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f1506,f3231])).

fof(f3231,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3180,f734])).

fof(f734,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f712,f701])).

fof(f701,plain,(
    ! [X2] : ~ r2_hidden(X2,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f700,f133])).

fof(f133,plain,(
    ! [X1] : k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X1)) = k4_xboole_0(sK1,X1) ),
    inference(superposition,[],[f68,f131])).

fof(f131,plain,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f116,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f116,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f700,plain,(
    ! [X2] : ~ r2_hidden(X2,k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f695,f105])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f695,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) ) ),
    inference(superposition,[],[f672,f370])).

fof(f370,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f360,f71])).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f360,plain,(
    k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f133,f204])).

fof(f204,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f187,f130])).

fof(f130,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f119,f118])).

fof(f118,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f64,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f119,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f64,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f187,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f176,f70])).

fof(f176,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f173,f64])).

fof(f173,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f84,f118])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f672,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,k4_xboole_0(sK1,X13))
      | ~ r2_hidden(X12,k3_xboole_0(sK1,X13)) ) ),
    inference(resolution,[],[f549,f353])).

fof(f353,plain,(
    ! [X12,X11] :
      ( r2_hidden(X12,k3_xboole_0(u1_struct_0(sK0),X11))
      | ~ r2_hidden(X12,k3_xboole_0(sK1,X11)) ) ),
    inference(superposition,[],[f104,f132])).

fof(f132,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X0)) = k3_xboole_0(sK1,X0) ),
    inference(superposition,[],[f67,f131])).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f549,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(u1_struct_0(sK0),X3))
      | ~ r2_hidden(X4,k4_xboole_0(sK1,X3)) ) ),
    inference(superposition,[],[f107,f359])).

fof(f359,plain,(
    ! [X8] : k4_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X8)) = k4_xboole_0(sK1,X8) ),
    inference(forward_demodulation,[],[f351,f93])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f351,plain,(
    ! [X8] : k4_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X8)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X8)) ),
    inference(superposition,[],[f93,f132])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f60,plain,(
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

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f712,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,k1_xboole_0,X5),X5)
      | k1_xboole_0 = X5 ) ),
    inference(forward_demodulation,[],[f708,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f708,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,k1_xboole_0,X5),X5)
      | k3_xboole_0(X4,k1_xboole_0) = X5 ) ),
    inference(resolution,[],[f703,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f703,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f702,f94])).

fof(f702,plain,(
    ! [X5] : ~ r2_hidden(X5,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f698,f105])).

fof(f698,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,k3_xboole_0(sK1,k1_xboole_0)) ) ),
    inference(superposition,[],[f672,f102])).

fof(f3180,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f2505,f2458])).

fof(f2458,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f2457])).

fof(f2457,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f2456,f276])).

fof(f276,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f148,f120])).

fof(f120,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f109,f63])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f148,plain,(
    ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f122,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f122,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f111,f63])).

fof(f111,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2456,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f2438,f373])).

fof(f373,plain,(
    ! [X1] : k3_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),X1)) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1) ),
    inference(superposition,[],[f68,f164])).

fof(f164,plain,(
    k2_pre_topc(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f147,f92])).

fof(f147,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f122,f82])).

fof(f2438,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(superposition,[],[f373,f860])).

fof(f860,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f415,f269])).

fof(f269,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f209,f158])).

fof(f158,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f65,f148])).

fof(f65,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f209,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f208,f63])).

fof(f208,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f206,f176])).

fof(f206,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f81,f130])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f415,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f194,f412])).

fof(f412,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f411,f256])).

fof(f256,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f246,f70])).

fof(f246,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f243,f193])).

fof(f193,plain,(
    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f180,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f176,f75])).

fof(f243,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f84,f129])).

fof(f129,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(backward_demodulation,[],[f124,f118])).

fof(f124,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f113,f63])).

fof(f113,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f411,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f394,f129])).

fof(f394,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f193,f69])).

fof(f194,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f181,f63])).

fof(f181,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f176,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f2505,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) ),
    inference(forward_demodulation,[],[f2480,f102])).

fof(f2480,plain,(
    ! [X2] : k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X2) ),
    inference(backward_demodulation,[],[f1876,f2468])).

fof(f2468,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f2420,f712])).

fof(f2420,plain,(
    ! [X2] : ~ r2_hidden(X2,k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2418,f1721])).

fof(f1721,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,k3_xboole_0(k1_xboole_0,X12))
      | r2_hidden(X11,sK1) ) ),
    inference(superposition,[],[f1474,f758])).

fof(f758,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f136,f735])).

fof(f735,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f712,f574])).

fof(f574,plain,(
    ! [X5] : ~ r2_hidden(X5,k5_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f571,f170])).

fof(f170,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(sK1,sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f107,f136])).

fof(f571,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k5_xboole_0(sK1,sK1))
      | r2_hidden(X5,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f104,f542])).

fof(f542,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f134,f131])).

fof(f134,plain,(
    ! [X2] : k3_xboole_0(k5_xboole_0(sK1,X2),u1_struct_0(sK0)) = k5_xboole_0(sK1,k3_xboole_0(X2,u1_struct_0(sK0))) ),
    inference(superposition,[],[f91,f131])).

fof(f91,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f136,plain,(
    k4_xboole_0(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f93,f131])).

fof(f1474,plain,(
    ! [X28,X29,X27] :
      ( ~ r2_hidden(X29,k3_xboole_0(k4_xboole_0(sK1,X27),X28))
      | r2_hidden(X29,sK1) ) ),
    inference(superposition,[],[f105,f362])).

fof(f362,plain,(
    ! [X0,X1] : k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),X0),X1)) = k3_xboole_0(k4_xboole_0(sK1,X0),X1) ),
    inference(superposition,[],[f67,f133])).

fof(f2418,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f107,f2354])).

fof(f2354,plain,(
    k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f330,f2353])).

fof(f2353,plain,(
    k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2345,f925])).

fof(f925,plain,(
    k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f776,f238])).

fof(f776,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f337,f735])).

fof(f337,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(k5_xboole_0(sK1,sK1),X1) ),
    inference(superposition,[],[f68,f177])).

fof(f177,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(resolution,[],[f168,f92])).

fof(f168,plain,(
    r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    inference(superposition,[],[f101,f136])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2345,plain,(
    k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f2252,f238])).

fof(f2252,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k4_xboole_0(sK1,X6),k4_xboole_0(sK1,X6)) ),
    inference(forward_demodulation,[],[f2251,f784])).

fof(f784,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k4_xboole_0(u1_struct_0(sK0),X1)) ),
    inference(backward_demodulation,[],[f566,f735])).

fof(f566,plain,(
    ! [X1] : k4_xboole_0(k5_xboole_0(sK1,sK1),X1) = k3_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(u1_struct_0(sK0),X1)) ),
    inference(superposition,[],[f68,f542])).

fof(f2251,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,k4_xboole_0(u1_struct_0(sK0),X6)) = k5_xboole_0(k4_xboole_0(sK1,X6),k4_xboole_0(sK1,X6)) ),
    inference(forward_demodulation,[],[f2238,f735])).

fof(f2238,plain,(
    ! [X6] : k3_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(u1_struct_0(sK0),X6)) = k5_xboole_0(k4_xboole_0(sK1,X6),k4_xboole_0(sK1,X6)) ),
    inference(superposition,[],[f364,f133])).

fof(f364,plain,(
    ! [X4,X5] : k3_xboole_0(k5_xboole_0(sK1,X5),k4_xboole_0(u1_struct_0(sK0),X4)) = k5_xboole_0(k4_xboole_0(sK1,X4),k3_xboole_0(X5,k4_xboole_0(u1_struct_0(sK0),X4))) ),
    inference(superposition,[],[f91,f133])).

fof(f330,plain,(
    k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f93,f275])).

fof(f275,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f271,f92])).

fof(f271,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f101,f238])).

fof(f1876,plain,(
    ! [X2] : k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))),X2) ),
    inference(backward_demodulation,[],[f1574,f1872])).

fof(f1872,plain,(
    k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1871,f925])).

fof(f1871,plain,(
    k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1870,f734])).

fof(f1870,plain,(
    k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1865,f133])).

fof(f1865,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[],[f363,f685])).

fof(f685,plain,(
    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f198,f186])).

fof(f186,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) ),
    inference(resolution,[],[f176,f72])).

fof(f198,plain,(
    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f192,f197])).

fof(f197,plain,(
    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f196,f149])).

fof(f149,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f122,f70])).

fof(f196,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f195,f130])).

fof(f195,plain,(
    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f182,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f176,f78])).

fof(f192,plain,(
    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f191,f128])).

fof(f128,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f125,f118])).

fof(f125,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f114,f63])).

fof(f114,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f191,plain,(
    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f179,f63])).

fof(f179,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f176,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f363,plain,(
    ! [X2,X3] : k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3) ),
    inference(superposition,[],[f68,f133])).

fof(f1574,plain,(
    ! [X2] : k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),X2) ),
    inference(backward_demodulation,[],[f1527,f1544])).

fof(f1544,plain,(
    ! [X13] : k5_xboole_0(sK1,k4_xboole_0(sK1,X13)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X13)) ),
    inference(superposition,[],[f93,f1491])).

fof(f1491,plain,(
    ! [X4] : k4_xboole_0(sK1,X4) = k3_xboole_0(sK1,k4_xboole_0(sK1,X4)) ),
    inference(superposition,[],[f1475,f133])).

fof(f1475,plain,(
    ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f1458,f370])).

fof(f1458,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k3_xboole_0(k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)),X0) ),
    inference(superposition,[],[f362,f204])).

fof(f1527,plain,(
    ! [X2] : k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),X2) ),
    inference(forward_demodulation,[],[f1510,f366])).

fof(f366,plain,(
    ! [X8] : k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X8)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X8)) ),
    inference(superposition,[],[f93,f133])).

fof(f1510,plain,(
    ! [X2] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),X2) = k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) ),
    inference(superposition,[],[f363,f468])).

fof(f468,plain,(
    k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f451,f163])).

fof(f163,plain,(
    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f150,f149])).

fof(f150,plain,(
    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f122,f69])).

fof(f451,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f288,f70])).

fof(f288,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f285,f122])).

fof(f285,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f84,f149])).

fof(f1506,plain,(
    ! [X12] : k4_xboole_0(sK1,k3_xboole_0(sK1,X12)) = k4_xboole_0(sK1,X12) ),
    inference(forward_demodulation,[],[f1499,f93])).

fof(f1499,plain,(
    ! [X12] : k4_xboole_0(sK1,k3_xboole_0(sK1,X12)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X12)) ),
    inference(superposition,[],[f93,f1475])).

fof(f238,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f121,f117])).

fof(f117,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(resolution,[],[f64,f72])).

fof(f121,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f110,f63])).

fof(f110,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f74])).

fof(f3708,plain,(
    ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f3347,f2460])).

fof(f2460,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f2459])).

fof(f2459,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f159,f2458])).

fof(f159,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f66,f148])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f3347,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f426,f3297])).

fof(f426,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f409,f412])).

fof(f409,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),sK0) ),
    inference(forward_demodulation,[],[f408,f129])).

fof(f408,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),sK0) ),
    inference(subsumption_resolution,[],[f390,f63])).

fof(f390,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f193,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3688,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f3412])).

fof(f3412,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f1287,f3297])).

fof(f1287,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1286,f63])).

fof(f1286,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1285,f176])).

fof(f1285,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1284,f62])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1284,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f77,f412])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29537)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (29559)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (29536)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (29551)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (29534)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29539)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (29555)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (29561)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (29541)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (29547)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29542)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29557)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (29553)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (29555)Refutation not found, incomplete strategy% (29555)------------------------------
% 0.21/0.53  % (29555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29555)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29555)Memory used [KB]: 10746
% 0.21/0.53  % (29555)Time elapsed: 0.072 s
% 0.21/0.53  % (29555)------------------------------
% 0.21/0.53  % (29555)------------------------------
% 0.21/0.53  % (29538)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29549)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29543)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (29533)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (29548)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (29545)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (29558)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (29532)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (29535)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (29560)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (29550)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (29556)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (29544)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (29546)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (29552)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (29562)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (29550)Refutation not found, incomplete strategy% (29550)------------------------------
% 0.21/0.57  % (29550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (29550)Memory used [KB]: 10618
% 0.21/0.57  % (29550)Time elapsed: 0.161 s
% 0.21/0.57  % (29550)------------------------------
% 0.21/0.57  % (29550)------------------------------
% 1.57/0.58  % (29554)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.16/0.69  % (29573)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.24/0.84  % (29537)Time limit reached!
% 3.24/0.84  % (29537)------------------------------
% 3.24/0.84  % (29537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.84  % (29537)Termination reason: Time limit
% 3.24/0.84  
% 3.24/0.84  % (29537)Memory used [KB]: 8443
% 3.24/0.84  % (29537)Time elapsed: 0.430 s
% 3.24/0.84  % (29537)------------------------------
% 3.24/0.84  % (29537)------------------------------
% 3.65/0.85  % (29587)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.01/0.91  % (29543)Time limit reached!
% 4.01/0.91  % (29543)------------------------------
% 4.01/0.91  % (29543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (29543)Termination reason: Time limit
% 4.01/0.91  % (29543)Termination phase: Saturation
% 4.01/0.91  
% 4.01/0.91  % (29543)Memory used [KB]: 11769
% 4.01/0.91  % (29543)Time elapsed: 0.500 s
% 4.01/0.91  % (29543)------------------------------
% 4.01/0.91  % (29543)------------------------------
% 4.01/0.92  % (29545)Time limit reached!
% 4.01/0.92  % (29545)------------------------------
% 4.01/0.92  % (29545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.93  % (29533)Time limit reached!
% 4.01/0.93  % (29533)------------------------------
% 4.01/0.93  % (29533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.93  % (29533)Termination reason: Time limit
% 4.01/0.93  % (29533)Termination phase: Saturation
% 4.01/0.93  
% 4.01/0.93  % (29533)Memory used [KB]: 7419
% 4.01/0.93  % (29533)Time elapsed: 0.500 s
% 4.01/0.93  % (29533)------------------------------
% 4.01/0.93  % (29533)------------------------------
% 4.01/0.93  % (29532)Time limit reached!
% 4.01/0.93  % (29532)------------------------------
% 4.01/0.93  % (29532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.93  % (29532)Termination reason: Time limit
% 4.01/0.93  
% 4.01/0.93  % (29532)Memory used [KB]: 3837
% 4.01/0.93  % (29532)Time elapsed: 0.518 s
% 4.01/0.93  % (29532)------------------------------
% 4.01/0.93  % (29532)------------------------------
% 4.01/0.94  % (29545)Termination reason: Time limit
% 4.01/0.94  
% 4.01/0.94  % (29545)Memory used [KB]: 8699
% 4.01/0.94  % (29545)Time elapsed: 0.516 s
% 4.01/0.94  % (29545)------------------------------
% 4.01/0.94  % (29545)------------------------------
% 4.42/1.01  % (29549)Time limit reached!
% 4.42/1.01  % (29549)------------------------------
% 4.42/1.01  % (29549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/1.01  % (29549)Termination reason: Time limit
% 4.42/1.01  
% 4.42/1.01  % (29549)Memory used [KB]: 14583
% 4.42/1.01  % (29549)Time elapsed: 0.603 s
% 4.42/1.01  % (29549)------------------------------
% 4.42/1.01  % (29549)------------------------------
% 4.42/1.01  % (29561)Time limit reached!
% 4.42/1.01  % (29561)------------------------------
% 4.42/1.01  % (29561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/1.01  % (29561)Termination reason: Time limit
% 4.42/1.01  % (29561)Termination phase: Saturation
% 4.42/1.01  
% 4.42/1.01  % (29561)Memory used [KB]: 7675
% 4.42/1.01  % (29561)Time elapsed: 0.600 s
% 4.42/1.01  % (29561)------------------------------
% 4.42/1.01  % (29561)------------------------------
% 4.42/1.03  % (29539)Time limit reached!
% 4.42/1.03  % (29539)------------------------------
% 4.42/1.03  % (29539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/1.03  % (29539)Termination reason: Time limit
% 4.42/1.03  % (29539)Termination phase: Saturation
% 4.42/1.03  
% 4.42/1.03  % (29539)Memory used [KB]: 11257
% 4.42/1.03  % (29539)Time elapsed: 0.600 s
% 4.42/1.03  % (29539)------------------------------
% 4.42/1.03  % (29539)------------------------------
% 4.42/1.03  % (29592)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.02/1.07  % (29594)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.02/1.07  % (29598)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.02/1.08  % (29596)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.02/1.09  % (29597)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.29/1.12  % (29600)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.29/1.12  % (29599)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.14/1.17  % (29601)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.53/1.23  % (29554)Time limit reached!
% 6.53/1.23  % (29554)------------------------------
% 6.53/1.23  % (29554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.53/1.23  % (29554)Termination reason: Time limit
% 6.53/1.23  % (29554)Termination phase: Saturation
% 6.53/1.23  
% 6.53/1.23  % (29554)Memory used [KB]: 6524
% 6.53/1.23  % (29554)Time elapsed: 0.800 s
% 6.53/1.23  % (29554)------------------------------
% 6.53/1.23  % (29554)------------------------------
% 7.55/1.36  % (29674)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.55/1.38  % (29594)Time limit reached!
% 7.55/1.38  % (29594)------------------------------
% 7.55/1.38  % (29594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.55/1.38  % (29596)Time limit reached!
% 7.55/1.38  % (29596)------------------------------
% 7.55/1.38  % (29596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.39  % (29596)Termination reason: Time limit
% 7.95/1.39  
% 7.95/1.39  % (29596)Memory used [KB]: 14200
% 7.95/1.39  % (29596)Time elapsed: 0.409 s
% 7.95/1.39  % (29596)------------------------------
% 7.95/1.39  % (29596)------------------------------
% 7.95/1.39  % (29594)Termination reason: Time limit
% 7.95/1.39  % (29594)Termination phase: Saturation
% 7.95/1.39  
% 7.95/1.39  % (29594)Memory used [KB]: 7036
% 7.95/1.39  % (29594)Time elapsed: 0.400 s
% 7.95/1.39  % (29594)------------------------------
% 7.95/1.39  % (29594)------------------------------
% 7.95/1.42  % (29534)Time limit reached!
% 7.95/1.42  % (29534)------------------------------
% 7.95/1.42  % (29534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.42  % (29534)Termination reason: Time limit
% 7.95/1.42  % (29534)Termination phase: Saturation
% 7.95/1.42  
% 7.95/1.42  % (29534)Memory used [KB]: 19957
% 7.95/1.42  % (29534)Time elapsed: 1.0000 s
% 7.95/1.42  % (29534)------------------------------
% 7.95/1.42  % (29534)------------------------------
% 8.47/1.48  % (29757)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.47/1.48  % (29758)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.15/1.55  % (29759)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.15/1.63  % (29559)Time limit reached!
% 9.15/1.63  % (29559)------------------------------
% 9.15/1.63  % (29559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.15/1.63  % (29559)Termination reason: Time limit
% 9.15/1.63  % (29559)Termination phase: Saturation
% 9.15/1.63  
% 9.15/1.63  % (29559)Memory used [KB]: 17270
% 9.15/1.63  % (29559)Time elapsed: 1.200 s
% 9.15/1.63  % (29559)------------------------------
% 9.15/1.63  % (29559)------------------------------
% 10.42/1.72  % (29548)Time limit reached!
% 10.42/1.72  % (29548)------------------------------
% 10.42/1.72  % (29548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.73  % (29548)Termination reason: Time limit
% 10.42/1.73  % (29548)Termination phase: Saturation
% 10.42/1.73  
% 10.42/1.73  % (29548)Memory used [KB]: 19189
% 10.42/1.73  % (29548)Time elapsed: 1.300 s
% 10.42/1.73  % (29548)------------------------------
% 10.42/1.73  % (29548)------------------------------
% 10.42/1.73  % (29557)Time limit reached!
% 10.42/1.73  % (29557)------------------------------
% 10.42/1.73  % (29557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.73  % (29557)Termination reason: Time limit
% 10.42/1.73  
% 10.42/1.73  % (29557)Memory used [KB]: 18677
% 10.42/1.73  % (29557)Time elapsed: 1.326 s
% 10.42/1.73  % (29557)------------------------------
% 10.42/1.73  % (29557)------------------------------
% 10.92/1.76  % (29834)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.02/1.78  % (29759)Refutation found. Thanks to Tanya!
% 11.02/1.78  % SZS status Theorem for theBenchmark
% 11.02/1.78  % SZS output start Proof for theBenchmark
% 11.02/1.78  fof(f3763,plain,(
% 11.02/1.78    $false),
% 11.02/1.78    inference(subsumption_resolution,[],[f3688,f3709])).
% 11.02/1.78  fof(f3709,plain,(
% 11.02/1.78    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 11.02/1.78    inference(forward_demodulation,[],[f3708,f3297])).
% 11.02/1.78  fof(f3297,plain,(
% 11.02/1.78    sK1 = k1_tops_1(sK0,sK1)),
% 11.02/1.78    inference(backward_demodulation,[],[f238,f3296])).
% 11.02/1.78  fof(f3296,plain,(
% 11.02/1.78    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 11.02/1.78    inference(forward_demodulation,[],[f3284,f102])).
% 11.02/1.78  fof(f102,plain,(
% 11.02/1.78    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.02/1.78    inference(cnf_transformation,[],[f10])).
% 11.02/1.78  fof(f10,axiom,(
% 11.02/1.78    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.02/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 11.02/1.78  fof(f3284,plain,(
% 11.02/1.78    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0)),
% 11.02/1.78    inference(superposition,[],[f1506,f3231])).
% 11.02/1.78  fof(f3231,plain,(
% 11.02/1.78    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 11.02/1.78    inference(forward_demodulation,[],[f3180,f734])).
% 11.02/1.78  fof(f734,plain,(
% 11.02/1.78    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 11.02/1.78    inference(resolution,[],[f712,f701])).
% 11.02/1.78  fof(f701,plain,(
% 11.02/1.78    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK1,sK1))) )),
% 11.02/1.78    inference(forward_demodulation,[],[f700,f133])).
% 11.02/1.78  fof(f133,plain,(
% 11.02/1.78    ( ! [X1] : (k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X1)) = k4_xboole_0(sK1,X1)) )),
% 11.02/1.78    inference(superposition,[],[f68,f131])).
% 11.02/1.78  fof(f131,plain,(
% 11.02/1.78    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))),
% 11.02/1.78    inference(resolution,[],[f116,f92])).
% 11.02/1.80  fof(f92,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 11.02/1.80    inference(cnf_transformation,[],[f44])).
% 11.02/1.80  fof(f44,plain,(
% 11.02/1.80    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.02/1.80    inference(ennf_transformation,[],[f7])).
% 11.02/1.80  fof(f7,axiom,(
% 11.02/1.80    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 11.02/1.80  fof(f116,plain,(
% 11.02/1.80    r1_tarski(sK1,u1_struct_0(sK0))),
% 11.02/1.80    inference(resolution,[],[f64,f82])).
% 11.02/1.80  fof(f82,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f51])).
% 11.02/1.80  fof(f51,plain,(
% 11.02/1.80    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.02/1.80    inference(nnf_transformation,[],[f18])).
% 11.02/1.80  fof(f18,axiom,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 11.02/1.80  fof(f64,plain,(
% 11.02/1.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(cnf_transformation,[],[f49])).
% 11.02/1.80  fof(f49,plain,(
% 11.02/1.80    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.02/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 11.02/1.80  fof(f47,plain,(
% 11.02/1.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.02/1.80    introduced(choice_axiom,[])).
% 11.02/1.80  fof(f48,plain,(
% 11.02/1.80    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 11.02/1.80    introduced(choice_axiom,[])).
% 11.02/1.80  fof(f46,plain,(
% 11.02/1.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.02/1.80    inference(flattening,[],[f45])).
% 11.02/1.80  fof(f45,plain,(
% 11.02/1.80    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.02/1.80    inference(nnf_transformation,[],[f30])).
% 11.02/1.80  fof(f30,plain,(
% 11.02/1.80    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.02/1.80    inference(flattening,[],[f29])).
% 11.02/1.80  fof(f29,plain,(
% 11.02/1.80    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.02/1.80    inference(ennf_transformation,[],[f27])).
% 11.02/1.80  fof(f27,negated_conjecture,(
% 11.02/1.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 11.02/1.80    inference(negated_conjecture,[],[f26])).
% 11.02/1.80  fof(f26,conjecture,(
% 11.02/1.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 11.02/1.80  fof(f68,plain,(
% 11.02/1.80    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f11])).
% 11.02/1.80  fof(f11,axiom,(
% 11.02/1.80    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 11.02/1.80  fof(f700,plain,(
% 11.02/1.80    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)))) )),
% 11.02/1.80    inference(subsumption_resolution,[],[f695,f105])).
% 11.02/1.80  fof(f105,plain,(
% 11.02/1.80    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 11.02/1.80    inference(equality_resolution,[],[f85])).
% 11.02/1.80  fof(f85,plain,(
% 11.02/1.80    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.02/1.80    inference(cnf_transformation,[],[f56])).
% 11.02/1.80  fof(f56,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 11.02/1.80  fof(f55,plain,(
% 11.02/1.80    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.02/1.80    introduced(choice_axiom,[])).
% 11.02/1.80  fof(f54,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(rectify,[],[f53])).
% 11.02/1.80  fof(f53,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(flattening,[],[f52])).
% 11.02/1.80  fof(f52,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(nnf_transformation,[],[f1])).
% 11.02/1.80  fof(f1,axiom,(
% 11.02/1.80    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 11.02/1.80  fof(f695,plain,(
% 11.02/1.80    ( ! [X2] : (~r2_hidden(X2,sK1) | ~r2_hidden(X2,k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)))) )),
% 11.02/1.80    inference(superposition,[],[f672,f370])).
% 11.02/1.80  fof(f370,plain,(
% 11.02/1.80    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f360,f71])).
% 11.02/1.80  fof(f71,plain,(
% 11.02/1.80    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.02/1.80    inference(cnf_transformation,[],[f28])).
% 11.02/1.80  fof(f28,plain,(
% 11.02/1.80    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.02/1.80    inference(rectify,[],[f3])).
% 11.02/1.80  fof(f3,axiom,(
% 11.02/1.80    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 11.02/1.80  fof(f360,plain,(
% 11.02/1.80    k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_xboole_0(sK1,sK1)),
% 11.02/1.80    inference(superposition,[],[f133,f204])).
% 11.02/1.80  fof(f204,plain,(
% 11.02/1.80    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f187,f130])).
% 11.02/1.80  fof(f130,plain,(
% 11.02/1.80    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f119,f118])).
% 11.02/1.80  fof(f118,plain,(
% 11.02/1.80    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 11.02/1.80    inference(resolution,[],[f64,f70])).
% 11.02/1.80  fof(f70,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f32])).
% 11.02/1.80  fof(f32,plain,(
% 11.02/1.80    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.02/1.80    inference(ennf_transformation,[],[f13])).
% 11.02/1.80  fof(f13,axiom,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 11.02/1.80  fof(f119,plain,(
% 11.02/1.80    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(resolution,[],[f64,f69])).
% 11.02/1.80  fof(f69,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 11.02/1.80    inference(cnf_transformation,[],[f31])).
% 11.02/1.80  fof(f31,plain,(
% 11.02/1.80    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.02/1.80    inference(ennf_transformation,[],[f15])).
% 11.02/1.80  fof(f15,axiom,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 11.02/1.80  fof(f187,plain,(
% 11.02/1.80    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(resolution,[],[f176,f70])).
% 11.02/1.80  fof(f176,plain,(
% 11.02/1.80    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f173,f64])).
% 11.02/1.80  fof(f173,plain,(
% 11.02/1.80    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(superposition,[],[f84,f118])).
% 11.02/1.80  fof(f84,plain,(
% 11.02/1.80    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.02/1.80    inference(cnf_transformation,[],[f43])).
% 11.02/1.80  fof(f43,plain,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.02/1.80    inference(ennf_transformation,[],[f14])).
% 11.02/1.80  fof(f14,axiom,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 11.02/1.80  fof(f672,plain,(
% 11.02/1.80    ( ! [X12,X13] : (~r2_hidden(X12,k4_xboole_0(sK1,X13)) | ~r2_hidden(X12,k3_xboole_0(sK1,X13))) )),
% 11.02/1.80    inference(resolution,[],[f549,f353])).
% 11.02/1.80  fof(f353,plain,(
% 11.02/1.80    ( ! [X12,X11] : (r2_hidden(X12,k3_xboole_0(u1_struct_0(sK0),X11)) | ~r2_hidden(X12,k3_xboole_0(sK1,X11))) )),
% 11.02/1.80    inference(superposition,[],[f104,f132])).
% 11.02/1.80  fof(f132,plain,(
% 11.02/1.80    ( ! [X0] : (k3_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X0)) = k3_xboole_0(sK1,X0)) )),
% 11.02/1.80    inference(superposition,[],[f67,f131])).
% 11.02/1.80  fof(f67,plain,(
% 11.02/1.80    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 11.02/1.80    inference(cnf_transformation,[],[f6])).
% 11.02/1.80  fof(f6,axiom,(
% 11.02/1.80    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 11.02/1.80  fof(f104,plain,(
% 11.02/1.80    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 11.02/1.80    inference(equality_resolution,[],[f86])).
% 11.02/1.80  fof(f86,plain,(
% 11.02/1.80    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.02/1.80    inference(cnf_transformation,[],[f56])).
% 11.02/1.80  fof(f549,plain,(
% 11.02/1.80    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(u1_struct_0(sK0),X3)) | ~r2_hidden(X4,k4_xboole_0(sK1,X3))) )),
% 11.02/1.80    inference(superposition,[],[f107,f359])).
% 11.02/1.80  fof(f359,plain,(
% 11.02/1.80    ( ! [X8] : (k4_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X8)) = k4_xboole_0(sK1,X8)) )),
% 11.02/1.80    inference(forward_demodulation,[],[f351,f93])).
% 11.02/1.80  fof(f93,plain,(
% 11.02/1.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.02/1.80    inference(cnf_transformation,[],[f4])).
% 11.02/1.80  fof(f4,axiom,(
% 11.02/1.80    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 11.02/1.80  fof(f351,plain,(
% 11.02/1.80    ( ! [X8] : (k4_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X8)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X8))) )),
% 11.02/1.80    inference(superposition,[],[f93,f132])).
% 11.02/1.80  fof(f107,plain,(
% 11.02/1.80    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 11.02/1.80    inference(equality_resolution,[],[f96])).
% 11.02/1.80  fof(f96,plain,(
% 11.02/1.80    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.02/1.80    inference(cnf_transformation,[],[f61])).
% 11.02/1.80  fof(f61,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).
% 11.02/1.80  fof(f60,plain,(
% 11.02/1.80    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 11.02/1.80    introduced(choice_axiom,[])).
% 11.02/1.80  fof(f59,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(rectify,[],[f58])).
% 11.02/1.80  fof(f58,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(flattening,[],[f57])).
% 11.02/1.80  fof(f57,plain,(
% 11.02/1.80    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.02/1.80    inference(nnf_transformation,[],[f2])).
% 11.02/1.80  fof(f2,axiom,(
% 11.02/1.80    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 11.02/1.80  fof(f712,plain,(
% 11.02/1.80    ( ! [X4,X5] : (r2_hidden(sK2(X4,k1_xboole_0,X5),X5) | k1_xboole_0 = X5) )),
% 11.02/1.80    inference(forward_demodulation,[],[f708,f94])).
% 11.02/1.80  fof(f94,plain,(
% 11.02/1.80    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f8])).
% 11.02/1.80  fof(f8,axiom,(
% 11.02/1.80    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 11.02/1.80  fof(f708,plain,(
% 11.02/1.80    ( ! [X4,X5] : (r2_hidden(sK2(X4,k1_xboole_0,X5),X5) | k3_xboole_0(X4,k1_xboole_0) = X5) )),
% 11.02/1.80    inference(resolution,[],[f703,f89])).
% 11.02/1.80  fof(f89,plain,(
% 11.02/1.80    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 11.02/1.80    inference(cnf_transformation,[],[f56])).
% 11.02/1.80  fof(f703,plain,(
% 11.02/1.80    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 11.02/1.80    inference(forward_demodulation,[],[f702,f94])).
% 11.02/1.80  fof(f702,plain,(
% 11.02/1.80    ( ! [X5] : (~r2_hidden(X5,k3_xboole_0(sK1,k1_xboole_0))) )),
% 11.02/1.80    inference(subsumption_resolution,[],[f698,f105])).
% 11.02/1.80  fof(f698,plain,(
% 11.02/1.80    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X5,k3_xboole_0(sK1,k1_xboole_0))) )),
% 11.02/1.80    inference(superposition,[],[f672,f102])).
% 11.02/1.80  fof(f3180,plain,(
% 11.02/1.80    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f2505,f2458])).
% 11.02/1.80  fof(f2458,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(duplicate_literal_removal,[],[f2457])).
% 11.02/1.80  fof(f2457,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(forward_demodulation,[],[f2456,f276])).
% 11.02/1.80  fof(f276,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f148,f120])).
% 11.02/1.80  fof(f120,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(subsumption_resolution,[],[f109,f63])).
% 11.02/1.80  fof(f63,plain,(
% 11.02/1.80    l1_pre_topc(sK0)),
% 11.02/1.80    inference(cnf_transformation,[],[f49])).
% 11.02/1.80  fof(f109,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f64,f73])).
% 11.02/1.80  fof(f73,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f34])).
% 11.02/1.80  fof(f34,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(ennf_transformation,[],[f22])).
% 11.02/1.80  fof(f22,axiom,(
% 11.02/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 11.02/1.80  fof(f148,plain,(
% 11.02/1.80    ( ! [X0] : (k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)) )),
% 11.02/1.80    inference(resolution,[],[f122,f72])).
% 11.02/1.80  fof(f72,plain,(
% 11.02/1.80    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f33])).
% 11.02/1.80  fof(f33,plain,(
% 11.02/1.80    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.02/1.80    inference(ennf_transformation,[],[f16])).
% 11.02/1.80  fof(f16,axiom,(
% 11.02/1.80    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 11.02/1.80  fof(f122,plain,(
% 11.02/1.80    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f111,f63])).
% 11.02/1.80  fof(f111,plain,(
% 11.02/1.80    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f64,f75])).
% 11.02/1.80  fof(f75,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f37])).
% 11.02/1.80  fof(f37,plain,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(flattening,[],[f36])).
% 11.02/1.80  fof(f36,plain,(
% 11.02/1.80    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.02/1.80    inference(ennf_transformation,[],[f19])).
% 11.02/1.80  fof(f19,axiom,(
% 11.02/1.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 11.02/1.80  fof(f2456,plain,(
% 11.02/1.80    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(forward_demodulation,[],[f2438,f373])).
% 11.02/1.80  fof(f373,plain,(
% 11.02/1.80    ( ! [X1] : (k3_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),X1)) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)) )),
% 11.02/1.80    inference(superposition,[],[f68,f164])).
% 11.02/1.80  fof(f164,plain,(
% 11.02/1.80    k2_pre_topc(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 11.02/1.80    inference(resolution,[],[f147,f92])).
% 11.02/1.80  fof(f147,plain,(
% 11.02/1.80    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 11.02/1.80    inference(resolution,[],[f122,f82])).
% 11.02/1.80  fof(f2438,plain,(
% 11.02/1.80    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(superposition,[],[f373,f860])).
% 11.02/1.80  fof(f860,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(resolution,[],[f415,f269])).
% 11.02/1.80  fof(f269,plain,(
% 11.02/1.80    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(resolution,[],[f209,f158])).
% 11.02/1.80  fof(f158,plain,(
% 11.02/1.80    v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(backward_demodulation,[],[f65,f148])).
% 11.02/1.80  fof(f65,plain,(
% 11.02/1.80    v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 11.02/1.80    inference(cnf_transformation,[],[f49])).
% 11.02/1.80  fof(f209,plain,(
% 11.02/1.80    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f208,f63])).
% 11.02/1.80  fof(f208,plain,(
% 11.02/1.80    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f206,f176])).
% 11.02/1.80  fof(f206,plain,(
% 11.02/1.80    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(superposition,[],[f81,f130])).
% 11.02/1.80  fof(f81,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f50])).
% 11.02/1.80  fof(f50,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(nnf_transformation,[],[f42])).
% 11.02/1.80  fof(f42,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(ennf_transformation,[],[f23])).
% 11.02/1.80  fof(f23,axiom,(
% 11.02/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 11.02/1.80  fof(f415,plain,(
% 11.02/1.80    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(backward_demodulation,[],[f194,f412])).
% 11.02/1.80  fof(f412,plain,(
% 11.02/1.80    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f411,f256])).
% 11.02/1.80  fof(f256,plain,(
% 11.02/1.80    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(resolution,[],[f246,f70])).
% 11.02/1.80  fof(f246,plain,(
% 11.02/1.80    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f243,f193])).
% 11.02/1.80  fof(f193,plain,(
% 11.02/1.80    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f180,f63])).
% 11.02/1.80  fof(f180,plain,(
% 11.02/1.80    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f176,f75])).
% 11.02/1.80  fof(f243,plain,(
% 11.02/1.80    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(superposition,[],[f84,f129])).
% 11.02/1.80  fof(f129,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 11.02/1.80    inference(backward_demodulation,[],[f124,f118])).
% 11.02/1.80  fof(f124,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f113,f63])).
% 11.02/1.80  fof(f113,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f64,f78])).
% 11.02/1.80  fof(f78,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f40])).
% 11.02/1.80  fof(f40,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(ennf_transformation,[],[f21])).
% 11.02/1.80  fof(f21,axiom,(
% 11.02/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 11.02/1.80  fof(f411,plain,(
% 11.02/1.80    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f394,f129])).
% 11.02/1.80  fof(f394,plain,(
% 11.02/1.80    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))))),
% 11.02/1.80    inference(resolution,[],[f193,f69])).
% 11.02/1.80  fof(f194,plain,(
% 11.02/1.80    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(subsumption_resolution,[],[f181,f63])).
% 11.02/1.80  fof(f181,plain,(
% 11.02/1.80    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f176,f76])).
% 11.02/1.80  fof(f76,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f39])).
% 11.02/1.80  fof(f39,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(flattening,[],[f38])).
% 11.02/1.80  fof(f38,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(ennf_transformation,[],[f20])).
% 11.02/1.80  fof(f20,axiom,(
% 11.02/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 11.02/1.80  fof(f2505,plain,(
% 11.02/1.80    ( ! [X2] : (k4_xboole_0(sK1,X2) = k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2))) )),
% 11.02/1.80    inference(forward_demodulation,[],[f2480,f102])).
% 11.02/1.80  fof(f2480,plain,(
% 11.02/1.80    ( ! [X2] : (k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X2)) )),
% 11.02/1.80    inference(backward_demodulation,[],[f1876,f2468])).
% 11.02/1.80  fof(f2468,plain,(
% 11.02/1.80    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(resolution,[],[f2420,f712])).
% 11.02/1.80  fof(f2420,plain,(
% 11.02/1.80    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)))) )),
% 11.02/1.80    inference(subsumption_resolution,[],[f2418,f1721])).
% 11.02/1.80  fof(f1721,plain,(
% 11.02/1.80    ( ! [X12,X11] : (~r2_hidden(X11,k3_xboole_0(k1_xboole_0,X12)) | r2_hidden(X11,sK1)) )),
% 11.02/1.80    inference(superposition,[],[f1474,f758])).
% 11.02/1.80  fof(f758,plain,(
% 11.02/1.80    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))),
% 11.02/1.80    inference(backward_demodulation,[],[f136,f735])).
% 11.02/1.80  fof(f735,plain,(
% 11.02/1.80    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 11.02/1.80    inference(resolution,[],[f712,f574])).
% 11.02/1.80  fof(f574,plain,(
% 11.02/1.80    ( ! [X5] : (~r2_hidden(X5,k5_xboole_0(sK1,sK1))) )),
% 11.02/1.80    inference(subsumption_resolution,[],[f571,f170])).
% 11.02/1.80  fof(f170,plain,(
% 11.02/1.80    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X1,u1_struct_0(sK0))) )),
% 11.02/1.80    inference(superposition,[],[f107,f136])).
% 11.02/1.80  fof(f571,plain,(
% 11.02/1.80    ( ! [X5] : (~r2_hidden(X5,k5_xboole_0(sK1,sK1)) | r2_hidden(X5,u1_struct_0(sK0))) )),
% 11.02/1.80    inference(superposition,[],[f104,f542])).
% 11.02/1.80  fof(f542,plain,(
% 11.02/1.80    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),u1_struct_0(sK0))),
% 11.02/1.80    inference(superposition,[],[f134,f131])).
% 11.02/1.80  fof(f134,plain,(
% 11.02/1.80    ( ! [X2] : (k3_xboole_0(k5_xboole_0(sK1,X2),u1_struct_0(sK0)) = k5_xboole_0(sK1,k3_xboole_0(X2,u1_struct_0(sK0)))) )),
% 11.02/1.80    inference(superposition,[],[f91,f131])).
% 11.02/1.80  fof(f91,plain,(
% 11.02/1.80    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f5])).
% 11.02/1.80  fof(f5,axiom,(
% 11.02/1.80    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 11.02/1.80  fof(f136,plain,(
% 11.02/1.80    k4_xboole_0(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1)),
% 11.02/1.80    inference(superposition,[],[f93,f131])).
% 11.02/1.80  fof(f1474,plain,(
% 11.02/1.80    ( ! [X28,X29,X27] : (~r2_hidden(X29,k3_xboole_0(k4_xboole_0(sK1,X27),X28)) | r2_hidden(X29,sK1)) )),
% 11.02/1.80    inference(superposition,[],[f105,f362])).
% 11.02/1.80  fof(f362,plain,(
% 11.02/1.80    ( ! [X0,X1] : (k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),X0),X1)) = k3_xboole_0(k4_xboole_0(sK1,X0),X1)) )),
% 11.02/1.80    inference(superposition,[],[f67,f133])).
% 11.02/1.80  fof(f2418,plain,(
% 11.02/1.80    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))) | ~r2_hidden(X2,sK1)) )),
% 11.02/1.80    inference(superposition,[],[f107,f2354])).
% 11.02/1.80  fof(f2354,plain,(
% 11.02/1.80    k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(backward_demodulation,[],[f330,f2353])).
% 11.02/1.80  fof(f2353,plain,(
% 11.02/1.80    k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f2345,f925])).
% 11.02/1.80  fof(f925,plain,(
% 11.02/1.80    k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) = k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f776,f238])).
% 11.02/1.80  fof(f776,plain,(
% 11.02/1.80    ( ! [X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1)) = k4_xboole_0(k1_xboole_0,X1)) )),
% 11.02/1.80    inference(backward_demodulation,[],[f337,f735])).
% 11.02/1.80  fof(f337,plain,(
% 11.02/1.80    ( ! [X1] : (k3_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(sK1,X1)) = k4_xboole_0(k5_xboole_0(sK1,sK1),X1)) )),
% 11.02/1.80    inference(superposition,[],[f68,f177])).
% 11.02/1.80  fof(f177,plain,(
% 11.02/1.80    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 11.02/1.80    inference(resolution,[],[f168,f92])).
% 11.02/1.80  fof(f168,plain,(
% 11.02/1.80    r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 11.02/1.80    inference(superposition,[],[f101,f136])).
% 11.02/1.80  fof(f101,plain,(
% 11.02/1.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f9])).
% 11.02/1.80  fof(f9,axiom,(
% 11.02/1.80    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 11.02/1.80  fof(f2345,plain,(
% 11.02/1.80    k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f2252,f238])).
% 11.02/1.80  fof(f2252,plain,(
% 11.02/1.80    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k4_xboole_0(sK1,X6),k4_xboole_0(sK1,X6))) )),
% 11.02/1.80    inference(forward_demodulation,[],[f2251,f784])).
% 11.02/1.80  fof(f784,plain,(
% 11.02/1.80    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k4_xboole_0(u1_struct_0(sK0),X1))) )),
% 11.02/1.80    inference(backward_demodulation,[],[f566,f735])).
% 11.02/1.80  fof(f566,plain,(
% 11.02/1.80    ( ! [X1] : (k4_xboole_0(k5_xboole_0(sK1,sK1),X1) = k3_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(u1_struct_0(sK0),X1))) )),
% 11.02/1.80    inference(superposition,[],[f68,f542])).
% 11.02/1.80  fof(f2251,plain,(
% 11.02/1.80    ( ! [X6] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(u1_struct_0(sK0),X6)) = k5_xboole_0(k4_xboole_0(sK1,X6),k4_xboole_0(sK1,X6))) )),
% 11.02/1.80    inference(forward_demodulation,[],[f2238,f735])).
% 11.02/1.80  fof(f2238,plain,(
% 11.02/1.80    ( ! [X6] : (k3_xboole_0(k5_xboole_0(sK1,sK1),k4_xboole_0(u1_struct_0(sK0),X6)) = k5_xboole_0(k4_xboole_0(sK1,X6),k4_xboole_0(sK1,X6))) )),
% 11.02/1.80    inference(superposition,[],[f364,f133])).
% 11.02/1.80  fof(f364,plain,(
% 11.02/1.80    ( ! [X4,X5] : (k3_xboole_0(k5_xboole_0(sK1,X5),k4_xboole_0(u1_struct_0(sK0),X4)) = k5_xboole_0(k4_xboole_0(sK1,X4),k3_xboole_0(X5,k4_xboole_0(u1_struct_0(sK0),X4)))) )),
% 11.02/1.80    inference(superposition,[],[f91,f133])).
% 11.02/1.80  fof(f330,plain,(
% 11.02/1.80    k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f93,f275])).
% 11.02/1.80  fof(f275,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 11.02/1.80    inference(resolution,[],[f271,f92])).
% 11.02/1.80  fof(f271,plain,(
% 11.02/1.80    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 11.02/1.80    inference(superposition,[],[f101,f238])).
% 11.02/1.80  fof(f1876,plain,(
% 11.02/1.80    ( ! [X2] : (k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1))),X2)) )),
% 11.02/1.80    inference(backward_demodulation,[],[f1574,f1872])).
% 11.02/1.80  fof(f1872,plain,(
% 11.02/1.80    k3_xboole_0(k1_xboole_0,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f1871,f925])).
% 11.02/1.80  fof(f1871,plain,(
% 11.02/1.80    k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f1870,f734])).
% 11.02/1.80  fof(f1870,plain,(
% 11.02/1.80    k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f1865,f133])).
% 11.02/1.80  fof(f1865,plain,(
% 11.02/1.80    k4_xboole_0(k4_xboole_0(sK1,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 11.02/1.80    inference(superposition,[],[f363,f685])).
% 11.02/1.80  fof(f685,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f198,f186])).
% 11.02/1.80  fof(f186,plain,(
% 11.02/1.80    ( ! [X0] : (k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)) )),
% 11.02/1.80    inference(resolution,[],[f176,f72])).
% 11.02/1.80  fof(f198,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(backward_demodulation,[],[f192,f197])).
% 11.02/1.80  fof(f197,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f196,f149])).
% 11.02/1.80  fof(f149,plain,(
% 11.02/1.80    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 11.02/1.80    inference(resolution,[],[f122,f70])).
% 11.02/1.80  fof(f196,plain,(
% 11.02/1.80    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f195,f130])).
% 11.02/1.80  fof(f195,plain,(
% 11.02/1.80    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))),
% 11.02/1.80    inference(subsumption_resolution,[],[f182,f63])).
% 11.02/1.80  fof(f182,plain,(
% 11.02/1.80    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f176,f78])).
% 11.02/1.80  fof(f192,plain,(
% 11.02/1.80    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(forward_demodulation,[],[f191,f128])).
% 11.02/1.80  fof(f128,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(backward_demodulation,[],[f125,f118])).
% 11.02/1.80  fof(f125,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 11.02/1.80    inference(subsumption_resolution,[],[f114,f63])).
% 11.02/1.80  fof(f114,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f64,f79])).
% 11.02/1.80  fof(f79,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f41])).
% 11.02/1.80  fof(f41,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(ennf_transformation,[],[f24])).
% 11.02/1.80  fof(f24,axiom,(
% 11.02/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 11.02/1.80  fof(f191,plain,(
% 11.02/1.80    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f179,f63])).
% 11.02/1.80  fof(f179,plain,(
% 11.02/1.80    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f176,f74])).
% 11.02/1.80  fof(f74,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f35])).
% 11.02/1.80  fof(f35,plain,(
% 11.02/1.80    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.02/1.80    inference(ennf_transformation,[],[f25])).
% 11.02/1.80  fof(f25,axiom,(
% 11.02/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 11.02/1.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 11.02/1.80  fof(f363,plain,(
% 11.02/1.80    ( ! [X2,X3] : (k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3)) )),
% 11.02/1.80    inference(superposition,[],[f68,f133])).
% 11.02/1.80  fof(f1574,plain,(
% 11.02/1.80    ( ! [X2] : (k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),X2)) )),
% 11.02/1.80    inference(backward_demodulation,[],[f1527,f1544])).
% 11.02/1.80  fof(f1544,plain,(
% 11.02/1.80    ( ! [X13] : (k5_xboole_0(sK1,k4_xboole_0(sK1,X13)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X13))) )),
% 11.02/1.80    inference(superposition,[],[f93,f1491])).
% 11.02/1.80  fof(f1491,plain,(
% 11.02/1.80    ( ! [X4] : (k4_xboole_0(sK1,X4) = k3_xboole_0(sK1,k4_xboole_0(sK1,X4))) )),
% 11.02/1.80    inference(superposition,[],[f1475,f133])).
% 11.02/1.80  fof(f1475,plain,(
% 11.02/1.80    ( ! [X0] : (k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 11.02/1.80    inference(forward_demodulation,[],[f1458,f370])).
% 11.02/1.80  fof(f1458,plain,(
% 11.02/1.80    ( ! [X0] : (k3_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k3_xboole_0(k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)),X0)) )),
% 11.02/1.80    inference(superposition,[],[f362,f204])).
% 11.02/1.80  fof(f1527,plain,(
% 11.02/1.80    ( ! [X2] : (k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),X2)) )),
% 11.02/1.80    inference(forward_demodulation,[],[f1510,f366])).
% 11.02/1.80  fof(f366,plain,(
% 11.02/1.80    ( ! [X8] : (k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X8)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X8))) )),
% 11.02/1.80    inference(superposition,[],[f93,f133])).
% 11.02/1.80  fof(f1510,plain,(
% 11.02/1.80    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),X2) = k3_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),X2))) )),
% 11.02/1.80    inference(superposition,[],[f363,f468])).
% 11.02/1.80  fof(f468,plain,(
% 11.02/1.80    k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 11.02/1.80    inference(forward_demodulation,[],[f451,f163])).
% 11.02/1.80  fof(f163,plain,(
% 11.02/1.80    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 11.02/1.80    inference(forward_demodulation,[],[f150,f149])).
% 11.02/1.80  fof(f150,plain,(
% 11.02/1.80    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 11.02/1.80    inference(resolution,[],[f122,f69])).
% 11.02/1.80  fof(f451,plain,(
% 11.02/1.80    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 11.02/1.80    inference(resolution,[],[f288,f70])).
% 11.02/1.80  fof(f288,plain,(
% 11.02/1.80    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(subsumption_resolution,[],[f285,f122])).
% 11.02/1.80  fof(f285,plain,(
% 11.02/1.80    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.02/1.80    inference(superposition,[],[f84,f149])).
% 11.02/1.80  fof(f1506,plain,(
% 11.02/1.80    ( ! [X12] : (k4_xboole_0(sK1,k3_xboole_0(sK1,X12)) = k4_xboole_0(sK1,X12)) )),
% 11.02/1.80    inference(forward_demodulation,[],[f1499,f93])).
% 11.02/1.80  fof(f1499,plain,(
% 11.02/1.80    ( ! [X12] : (k4_xboole_0(sK1,k3_xboole_0(sK1,X12)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X12))) )),
% 11.02/1.80    inference(superposition,[],[f93,f1475])).
% 11.02/1.80  fof(f238,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(superposition,[],[f121,f117])).
% 11.02/1.80  fof(f117,plain,(
% 11.02/1.80    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 11.02/1.80    inference(resolution,[],[f64,f72])).
% 11.02/1.80  fof(f121,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 11.02/1.80    inference(subsumption_resolution,[],[f110,f63])).
% 11.02/1.80  fof(f110,plain,(
% 11.02/1.80    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f64,f74])).
% 11.02/1.80  fof(f3708,plain,(
% 11.02/1.80    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f3347,f2460])).
% 11.02/1.80  fof(f2460,plain,(
% 11.02/1.80    ~v3_pre_topc(sK1,sK0)),
% 11.02/1.80    inference(trivial_inequality_removal,[],[f2459])).
% 11.02/1.80  fof(f2459,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 11.02/1.80    inference(backward_demodulation,[],[f159,f2458])).
% 11.02/1.80  fof(f159,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 11.02/1.80    inference(backward_demodulation,[],[f66,f148])).
% 11.02/1.80  fof(f66,plain,(
% 11.02/1.80    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 11.02/1.80    inference(cnf_transformation,[],[f49])).
% 11.02/1.80  fof(f3347,plain,(
% 11.02/1.80    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),sK0)),
% 11.02/1.80    inference(backward_demodulation,[],[f426,f3297])).
% 11.02/1.80  fof(f426,plain,(
% 11.02/1.80    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 11.02/1.80    inference(backward_demodulation,[],[f409,f412])).
% 11.02/1.80  fof(f409,plain,(
% 11.02/1.80    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v4_pre_topc(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),sK0)),
% 11.02/1.80    inference(forward_demodulation,[],[f408,f129])).
% 11.02/1.80  fof(f408,plain,(
% 11.02/1.80    ~v4_pre_topc(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),sK0) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f390,f63])).
% 11.02/1.80  fof(f390,plain,(
% 11.02/1.80    ~v4_pre_topc(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),sK0) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),sK0) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(resolution,[],[f193,f80])).
% 11.02/1.80  fof(f80,plain,(
% 11.02/1.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f50])).
% 11.02/1.80  fof(f3688,plain,(
% 11.02/1.80    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 11.02/1.80    inference(trivial_inequality_removal,[],[f3412])).
% 11.02/1.80  fof(f3412,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 11.02/1.80    inference(backward_demodulation,[],[f1287,f3297])).
% 11.02/1.80  fof(f1287,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f1286,f63])).
% 11.02/1.80  fof(f1286,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f1285,f176])).
% 11.02/1.80  fof(f1285,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(subsumption_resolution,[],[f1284,f62])).
% 11.02/1.80  fof(f62,plain,(
% 11.02/1.80    v2_pre_topc(sK0)),
% 11.02/1.80    inference(cnf_transformation,[],[f49])).
% 11.02/1.80  fof(f1284,plain,(
% 11.02/1.80    k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 11.02/1.80    inference(superposition,[],[f77,f412])).
% 11.02/1.80  fof(f77,plain,(
% 11.02/1.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.02/1.80    inference(cnf_transformation,[],[f39])).
% 11.02/1.80  % SZS output end Proof for theBenchmark
% 11.02/1.80  % (29759)------------------------------
% 11.02/1.80  % (29759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.02/1.80  % (29759)Termination reason: Refutation
% 11.02/1.80  
% 11.02/1.80  % (29759)Memory used [KB]: 4221
% 11.02/1.80  % (29759)Time elapsed: 0.346 s
% 11.02/1.80  % (29759)------------------------------
% 11.02/1.80  % (29759)------------------------------
% 11.02/1.80  % (29530)Success in time 1.422 s
%------------------------------------------------------------------------------
