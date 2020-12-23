%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 4.22s
% Output     : Refutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 168 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 ( 496 expanded)
%              Number of equality atoms :   46 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8397,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8396,f1447])).

fof(f1447,plain,(
    ! [X6,X8,X7] : r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f46,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f8396,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f7404,f8390])).

fof(f8390,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f8368,f5871])).

fof(f5871,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f535,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f535,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X3))
      | k4_xboole_0(X3,X4) = k3_subset_1(X3,X4) ) ),
    inference(subsumption_resolution,[],[f532,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f532,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X3,X4) = k3_subset_1(X3,X4)
      | ~ r2_hidden(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f8368,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f8274,f130])).

fof(f130,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f99,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f99,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f53,f89])).

fof(f89,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f8274,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK1,X0),k2_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f8246,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f8246,plain,(
    ! [X28] : r1_tarski(k4_xboole_0(k2_xboole_0(sK1,X28),sK0),X28) ),
    inference(superposition,[],[f8012,f122])).

fof(f122,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f98,f48])).

fof(f98,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f53,f88])).

fof(f88,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f85,f70])).

fof(f85,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f8012,plain,(
    ! [X45,X46,X44] : r1_tarski(k4_xboole_0(k2_xboole_0(X44,X45),k2_xboole_0(X46,X44)),X45) ),
    inference(forward_demodulation,[],[f8011,f64])).

fof(f8011,plain,(
    ! [X45,X46,X44] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),X44),X45) ),
    inference(forward_demodulation,[],[f7958,f100])).

fof(f100,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f93,f48])).

fof(f93,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f7958,plain,(
    ! [X45,X46,X44] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),X44),k2_xboole_0(X45,k1_xboole_0)) ),
    inference(superposition,[],[f1453,f161])).

fof(f161,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f47,f95])).

fof(f95,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(resolution,[],[f53,f46])).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1453,plain,(
    ! [X26,X27,X25] : r1_tarski(k4_xboole_0(X25,X26),k2_xboole_0(X27,k4_xboole_0(X25,k2_xboole_0(X26,X27)))) ),
    inference(superposition,[],[f233,f64])).

fof(f233,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(resolution,[],[f65,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7404,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f533,f7396])).

fof(f7396,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f4488,f40])).

fof(f4488,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f66,f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f533,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f41,f528])).

fof(f528,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f55,f39])).

fof(f41,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (21754)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  % (21744)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (21762)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (21755)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (21748)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (21747)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (21765)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (21749)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (21757)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (21756)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (21766)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (21746)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (21761)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (21758)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (21764)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (21750)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (21768)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (21751)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (21753)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (21752)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (21763)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (21769)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (21767)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (21760)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.56  % (21745)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (21759)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 2.12/0.71  % (21753)Refutation not found, incomplete strategy% (21753)------------------------------
% 2.12/0.71  % (21753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (21753)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (21753)Memory used [KB]: 6140
% 2.12/0.71  % (21753)Time elapsed: 0.310 s
% 2.12/0.71  % (21753)------------------------------
% 2.12/0.71  % (21753)------------------------------
% 4.22/0.90  % (21747)Refutation found. Thanks to Tanya!
% 4.22/0.90  % SZS status Theorem for theBenchmark
% 4.22/0.91  % SZS output start Proof for theBenchmark
% 4.22/0.91  fof(f8397,plain,(
% 4.22/0.91    $false),
% 4.22/0.91    inference(subsumption_resolution,[],[f8396,f1447])).
% 4.22/0.91  fof(f1447,plain,(
% 4.22/0.91    ( ! [X6,X8,X7] : (r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),k4_xboole_0(X6,X7))) )),
% 4.22/0.91    inference(superposition,[],[f46,f64])).
% 4.22/0.91  fof(f64,plain,(
% 4.22/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.22/0.91    inference(cnf_transformation,[],[f6])).
% 4.22/0.91  fof(f6,axiom,(
% 4.22/0.91    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.22/0.91  fof(f46,plain,(
% 4.22/0.91    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f5])).
% 4.22/0.91  fof(f5,axiom,(
% 4.22/0.91    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.22/0.91  fof(f8396,plain,(
% 4.22/0.91    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 4.22/0.91    inference(backward_demodulation,[],[f7404,f8390])).
% 4.22/0.91  fof(f8390,plain,(
% 4.22/0.91    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 4.22/0.91    inference(resolution,[],[f8368,f5871])).
% 4.22/0.91  fof(f5871,plain,(
% 4.22/0.91    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 4.22/0.91    inference(resolution,[],[f535,f69])).
% 4.22/0.91  fof(f69,plain,(
% 4.22/0.91    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 4.22/0.91    inference(equality_resolution,[],[f61])).
% 4.22/0.91  fof(f61,plain,(
% 4.22/0.91    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 4.22/0.91    inference(cnf_transformation,[],[f38])).
% 4.22/0.91  fof(f38,plain,(
% 4.22/0.91    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.22/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 4.22/0.91  fof(f37,plain,(
% 4.22/0.91    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 4.22/0.91    introduced(choice_axiom,[])).
% 4.22/0.91  fof(f36,plain,(
% 4.22/0.91    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.22/0.91    inference(rectify,[],[f35])).
% 4.22/0.91  fof(f35,plain,(
% 4.22/0.91    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.22/0.91    inference(nnf_transformation,[],[f10])).
% 4.22/0.91  fof(f10,axiom,(
% 4.22/0.91    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 4.22/0.91  fof(f535,plain,(
% 4.22/0.91    ( ! [X4,X3] : (~r2_hidden(X4,k1_zfmisc_1(X3)) | k4_xboole_0(X3,X4) = k3_subset_1(X3,X4)) )),
% 4.22/0.91    inference(subsumption_resolution,[],[f532,f42])).
% 4.22/0.91  fof(f42,plain,(
% 4.22/0.91    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 4.22/0.91    inference(cnf_transformation,[],[f14])).
% 4.22/0.91  fof(f14,axiom,(
% 4.22/0.91    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 4.22/0.91  fof(f532,plain,(
% 4.22/0.91    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_subset_1(X3,X4) | ~r2_hidden(X4,k1_zfmisc_1(X3)) | v1_xboole_0(k1_zfmisc_1(X3))) )),
% 4.22/0.91    inference(resolution,[],[f55,f50])).
% 4.22/0.91  fof(f50,plain,(
% 4.22/0.91    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f32])).
% 4.22/0.91  fof(f32,plain,(
% 4.22/0.91    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 4.22/0.91    inference(nnf_transformation,[],[f21])).
% 4.22/0.91  fof(f21,plain,(
% 4.22/0.91    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.22/0.91    inference(ennf_transformation,[],[f11])).
% 4.22/0.91  fof(f11,axiom,(
% 4.22/0.91    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 4.22/0.91  fof(f55,plain,(
% 4.22/0.91    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f24])).
% 4.22/0.91  fof(f24,plain,(
% 4.22/0.91    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.22/0.91    inference(ennf_transformation,[],[f12])).
% 4.22/0.91  fof(f12,axiom,(
% 4.22/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 4.22/0.91  fof(f8368,plain,(
% 4.22/0.91    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 4.22/0.91    inference(superposition,[],[f8274,f130])).
% 4.22/0.91  fof(f130,plain,(
% 4.22/0.91    sK0 = k2_xboole_0(sK0,sK2)),
% 4.22/0.91    inference(superposition,[],[f99,f48])).
% 4.22/0.91  fof(f48,plain,(
% 4.22/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f1])).
% 4.22/0.91  fof(f1,axiom,(
% 4.22/0.91    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.22/0.91  fof(f99,plain,(
% 4.22/0.91    sK0 = k2_xboole_0(sK2,sK0)),
% 4.22/0.91    inference(resolution,[],[f53,f89])).
% 4.22/0.91  fof(f89,plain,(
% 4.22/0.91    r1_tarski(sK2,sK0)),
% 4.22/0.91    inference(resolution,[],[f86,f70])).
% 4.22/0.91  fof(f70,plain,(
% 4.22/0.91    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 4.22/0.91    inference(equality_resolution,[],[f60])).
% 4.22/0.91  fof(f60,plain,(
% 4.22/0.91    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.22/0.91    inference(cnf_transformation,[],[f38])).
% 4.22/0.91  fof(f86,plain,(
% 4.22/0.91    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(subsumption_resolution,[],[f83,f42])).
% 4.22/0.91  fof(f83,plain,(
% 4.22/0.91    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(resolution,[],[f49,f40])).
% 4.22/0.91  fof(f40,plain,(
% 4.22/0.91    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(cnf_transformation,[],[f31])).
% 4.22/0.91  fof(f31,plain,(
% 4.22/0.91    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f30,f29])).
% 4.22/0.91  fof(f29,plain,(
% 4.22/0.91    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 4.22/0.91    introduced(choice_axiom,[])).
% 4.22/0.91  fof(f30,plain,(
% 4.22/0.91    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 4.22/0.91    introduced(choice_axiom,[])).
% 4.22/0.91  fof(f20,plain,(
% 4.22/0.91    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.22/0.91    inference(ennf_transformation,[],[f19])).
% 4.22/0.91  fof(f19,negated_conjecture,(
% 4.22/0.91    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 4.22/0.91    inference(negated_conjecture,[],[f18])).
% 4.22/0.91  fof(f18,conjecture,(
% 4.22/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 4.22/0.91  fof(f49,plain,(
% 4.22/0.91    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f32])).
% 4.22/0.91  fof(f53,plain,(
% 4.22/0.91    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.22/0.91    inference(cnf_transformation,[],[f22])).
% 4.22/0.91  fof(f22,plain,(
% 4.22/0.91    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.22/0.91    inference(ennf_transformation,[],[f3])).
% 4.22/0.91  fof(f3,axiom,(
% 4.22/0.91    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.22/0.91  fof(f8274,plain,(
% 4.22/0.91    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,X0),k2_xboole_0(sK0,X0))) )),
% 4.22/0.91    inference(resolution,[],[f8246,f65])).
% 4.22/0.91  fof(f65,plain,(
% 4.22/0.91    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.22/0.91    inference(cnf_transformation,[],[f26])).
% 4.22/0.91  fof(f26,plain,(
% 4.22/0.91    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.22/0.91    inference(ennf_transformation,[],[f7])).
% 4.22/0.91  fof(f7,axiom,(
% 4.22/0.91    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.22/0.91  fof(f8246,plain,(
% 4.22/0.91    ( ! [X28] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK1,X28),sK0),X28)) )),
% 4.22/0.91    inference(superposition,[],[f8012,f122])).
% 4.22/0.91  fof(f122,plain,(
% 4.22/0.91    sK0 = k2_xboole_0(sK0,sK1)),
% 4.22/0.91    inference(superposition,[],[f98,f48])).
% 4.22/0.91  fof(f98,plain,(
% 4.22/0.91    sK0 = k2_xboole_0(sK1,sK0)),
% 4.22/0.91    inference(resolution,[],[f53,f88])).
% 4.22/0.91  fof(f88,plain,(
% 4.22/0.91    r1_tarski(sK1,sK0)),
% 4.22/0.91    inference(resolution,[],[f85,f70])).
% 4.22/0.91  fof(f85,plain,(
% 4.22/0.91    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(subsumption_resolution,[],[f82,f42])).
% 4.22/0.91  fof(f82,plain,(
% 4.22/0.91    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(resolution,[],[f49,f39])).
% 4.22/0.91  fof(f39,plain,(
% 4.22/0.91    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.22/0.91    inference(cnf_transformation,[],[f31])).
% 4.22/0.91  fof(f8012,plain,(
% 4.22/0.91    ( ! [X45,X46,X44] : (r1_tarski(k4_xboole_0(k2_xboole_0(X44,X45),k2_xboole_0(X46,X44)),X45)) )),
% 4.22/0.91    inference(forward_demodulation,[],[f8011,f64])).
% 4.22/0.91  fof(f8011,plain,(
% 4.22/0.91    ( ! [X45,X46,X44] : (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),X44),X45)) )),
% 4.22/0.91    inference(forward_demodulation,[],[f7958,f100])).
% 4.22/0.91  fof(f100,plain,(
% 4.22/0.91    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 4.22/0.91    inference(superposition,[],[f93,f48])).
% 4.22/0.91  fof(f93,plain,(
% 4.22/0.91    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.22/0.91    inference(resolution,[],[f53,f43])).
% 4.22/0.91  fof(f43,plain,(
% 4.22/0.91    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f4])).
% 4.22/0.91  fof(f4,axiom,(
% 4.22/0.91    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.22/0.91  fof(f7958,plain,(
% 4.22/0.91    ( ! [X45,X46,X44] : (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),X44),k2_xboole_0(X45,k1_xboole_0))) )),
% 4.22/0.91    inference(superposition,[],[f1453,f161])).
% 4.22/0.91  fof(f161,plain,(
% 4.22/0.91    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8)) )),
% 4.22/0.91    inference(superposition,[],[f47,f95])).
% 4.22/0.91  fof(f95,plain,(
% 4.22/0.91    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 4.22/0.91    inference(resolution,[],[f53,f46])).
% 4.22/0.91  fof(f47,plain,(
% 4.22/0.91    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.22/0.91    inference(cnf_transformation,[],[f8])).
% 4.22/0.91  fof(f8,axiom,(
% 4.22/0.91    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.22/0.91  fof(f1453,plain,(
% 4.22/0.91    ( ! [X26,X27,X25] : (r1_tarski(k4_xboole_0(X25,X26),k2_xboole_0(X27,k4_xboole_0(X25,k2_xboole_0(X26,X27))))) )),
% 4.22/0.91    inference(superposition,[],[f233,f64])).
% 4.22/0.91  fof(f233,plain,(
% 4.22/0.91    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 4.22/0.91    inference(resolution,[],[f65,f67])).
% 4.22/0.91  fof(f67,plain,(
% 4.22/0.91    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.22/0.91    inference(equality_resolution,[],[f58])).
% 4.22/0.91  fof(f58,plain,(
% 4.22/0.91    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.22/0.91    inference(cnf_transformation,[],[f34])).
% 4.22/0.91  fof(f34,plain,(
% 4.22/0.91    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.22/0.91    inference(flattening,[],[f33])).
% 4.22/0.91  fof(f33,plain,(
% 4.22/0.91    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.22/0.91    inference(nnf_transformation,[],[f2])).
% 4.22/0.91  fof(f2,axiom,(
% 4.22/0.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.22/0.91  fof(f7404,plain,(
% 4.22/0.91    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 4.22/0.91    inference(backward_demodulation,[],[f533,f7396])).
% 4.22/0.91  fof(f7396,plain,(
% 4.22/0.91    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 4.22/0.91    inference(resolution,[],[f4488,f40])).
% 4.22/0.91  fof(f4488,plain,(
% 4.22/0.91    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0)) )),
% 4.22/0.91    inference(resolution,[],[f66,f39])).
% 4.22/0.91  fof(f66,plain,(
% 4.22/0.91    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 4.22/0.91    inference(cnf_transformation,[],[f28])).
% 4.22/0.91  fof(f28,plain,(
% 4.22/0.91    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.22/0.91    inference(flattening,[],[f27])).
% 4.22/0.91  fof(f27,plain,(
% 4.22/0.91    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.22/0.91    inference(ennf_transformation,[],[f16])).
% 4.22/0.91  fof(f16,axiom,(
% 4.22/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.22/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.22/0.91  fof(f533,plain,(
% 4.22/0.91    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 4.22/0.91    inference(backward_demodulation,[],[f41,f528])).
% 4.22/0.91  fof(f528,plain,(
% 4.22/0.91    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 4.22/0.91    inference(resolution,[],[f55,f39])).
% 4.22/0.91  fof(f41,plain,(
% 4.22/0.91    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 4.22/0.91    inference(cnf_transformation,[],[f31])).
% 4.22/0.91  % SZS output end Proof for theBenchmark
% 4.22/0.91  % (21747)------------------------------
% 4.22/0.91  % (21747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.91  % (21747)Termination reason: Refutation
% 4.22/0.91  
% 4.22/0.91  % (21747)Memory used [KB]: 11385
% 4.22/0.91  % (21747)Time elapsed: 0.468 s
% 4.22/0.91  % (21747)------------------------------
% 4.22/0.91  % (21747)------------------------------
% 4.22/0.91  % (21743)Success in time 0.549 s
%------------------------------------------------------------------------------
