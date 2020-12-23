%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 3.14s
% Output     : Refutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 148 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  228 ( 503 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3081,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3080,f920])).

fof(f920,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f580,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f580,plain,(
    ~ r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f575,f41])).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f575,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f307,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f307,plain,(
    ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f306,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f306,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f300,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f300,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f203,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f38,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f203,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f196,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f196,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f110,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f110,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f106,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f106,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f40,f68])).

fof(f68,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f38,f49])).

fof(f40,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3080,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f3064,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3064,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(resolution,[],[f2106,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(X0,sK2),sK0)
      | r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f58,f113])).

fof(f113,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f94,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f94,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f81,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f77,f41])).

fof(f77,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2106,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(k2_xboole_0(X3,sK1),X3),sK0) ),
    inference(resolution,[],[f543,f63])).

fof(f543,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k2_xboole_0(X4,sK1))
      | r1_tarski(k4_xboole_0(X3,X4),sK0) ) ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f102,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f90,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f90,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f73,f65])).

fof(f73,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f69,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:39:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (15739)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (15732)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (15714)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (15735)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (15742)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (15736)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (15713)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15718)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (15734)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (15712)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (15743)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (15740)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (15737)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (15741)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (15716)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (15738)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (15715)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (15717)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.38/0.54  % (15719)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.38/0.54  % (15745)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.38/0.54  % (15720)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.54  % (15744)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.38/0.54  % (15726)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.38/0.55  % (15733)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.38/0.56  % (15729)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.55/0.56  % (15723)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 3.14/0.77  % (15738)Refutation found. Thanks to Tanya!
% 3.14/0.77  % SZS status Theorem for theBenchmark
% 3.14/0.77  % SZS output start Proof for theBenchmark
% 3.14/0.77  fof(f3081,plain,(
% 3.14/0.77    $false),
% 3.14/0.77    inference(subsumption_resolution,[],[f3080,f920])).
% 3.14/0.77  fof(f920,plain,(
% 3.14/0.77    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 3.14/0.77    inference(resolution,[],[f580,f64])).
% 3.14/0.77  fof(f64,plain,(
% 3.14/0.77    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.14/0.77    inference(equality_resolution,[],[f54])).
% 3.14/0.77  fof(f54,plain,(
% 3.14/0.77    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.14/0.77    inference(cnf_transformation,[],[f37])).
% 3.14/0.77  fof(f37,plain,(
% 3.14/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.14/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 3.14/0.77  fof(f36,plain,(
% 3.14/0.77    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.14/0.77    introduced(choice_axiom,[])).
% 3.14/0.77  fof(f35,plain,(
% 3.14/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.14/0.77    inference(rectify,[],[f34])).
% 3.14/0.77  fof(f34,plain,(
% 3.14/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.14/0.77    inference(nnf_transformation,[],[f9])).
% 3.14/0.77  fof(f9,axiom,(
% 3.14/0.77    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.14/0.77  fof(f580,plain,(
% 3.14/0.77    ~r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(subsumption_resolution,[],[f575,f41])).
% 3.14/0.77  fof(f41,plain,(
% 3.14/0.77    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.14/0.77    inference(cnf_transformation,[],[f12])).
% 3.14/0.77  fof(f12,axiom,(
% 3.14/0.77    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.14/0.77  fof(f575,plain,(
% 3.14/0.77    ~r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(resolution,[],[f307,f45])).
% 3.14/0.77  fof(f45,plain,(
% 3.14/0.77    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f31])).
% 3.14/0.77  fof(f31,plain,(
% 3.14/0.77    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.14/0.77    inference(nnf_transformation,[],[f17])).
% 3.14/0.77  fof(f17,plain,(
% 3.14/0.77    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.14/0.77    inference(ennf_transformation,[],[f10])).
% 3.14/0.77  fof(f10,axiom,(
% 3.14/0.77    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 3.14/0.77  fof(f307,plain,(
% 3.14/0.77    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(subsumption_resolution,[],[f306,f39])).
% 3.14/0.77  fof(f39,plain,(
% 3.14/0.77    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(cnf_transformation,[],[f30])).
% 3.14/0.77  fof(f30,plain,(
% 3.14/0.77    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29,f28])).
% 3.14/0.77  fof(f28,plain,(
% 3.14/0.77    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 3.14/0.77    introduced(choice_axiom,[])).
% 3.14/0.77  fof(f29,plain,(
% 3.14/0.77    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 3.14/0.77    introduced(choice_axiom,[])).
% 3.14/0.77  fof(f16,plain,(
% 3.14/0.77    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.14/0.77    inference(ennf_transformation,[],[f15])).
% 3.14/0.77  fof(f15,negated_conjecture,(
% 3.14/0.77    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 3.14/0.77    inference(negated_conjecture,[],[f14])).
% 3.14/0.77  fof(f14,conjecture,(
% 3.14/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 3.14/0.77  fof(f306,plain,(
% 3.14/0.77    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(subsumption_resolution,[],[f300,f42])).
% 3.14/0.77  fof(f42,plain,(
% 3.14/0.77    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.14/0.77    inference(cnf_transformation,[],[f8])).
% 3.14/0.77  fof(f8,axiom,(
% 3.14/0.77    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.14/0.77  fof(f300,plain,(
% 3.14/0.77    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(superposition,[],[f203,f66])).
% 3.14/0.77  fof(f66,plain,(
% 3.14/0.77    ( ! [X0] : (k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 3.14/0.77    inference(resolution,[],[f38,f60])).
% 3.14/0.77  fof(f60,plain,(
% 3.14/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.14/0.77    inference(cnf_transformation,[],[f25])).
% 3.14/0.77  fof(f25,plain,(
% 3.14/0.77    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.14/0.77    inference(flattening,[],[f24])).
% 3.14/0.77  fof(f24,plain,(
% 3.14/0.77    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.14/0.77    inference(ennf_transformation,[],[f13])).
% 3.14/0.77  fof(f13,axiom,(
% 3.14/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.14/0.77  fof(f38,plain,(
% 3.14/0.77    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(cnf_transformation,[],[f30])).
% 3.14/0.77  fof(f203,plain,(
% 3.14/0.77    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))),
% 3.14/0.77    inference(subsumption_resolution,[],[f196,f63])).
% 3.14/0.77  fof(f63,plain,(
% 3.14/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.14/0.77    inference(equality_resolution,[],[f50])).
% 3.14/0.77  fof(f50,plain,(
% 3.14/0.77    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.14/0.77    inference(cnf_transformation,[],[f33])).
% 3.14/0.77  fof(f33,plain,(
% 3.14/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.77    inference(flattening,[],[f32])).
% 3.14/0.77  fof(f32,plain,(
% 3.14/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.77    inference(nnf_transformation,[],[f2])).
% 3.14/0.77  fof(f2,axiom,(
% 3.14/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.14/0.77  fof(f196,plain,(
% 3.14/0.77    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | ~r1_tarski(sK0,sK0)),
% 3.14/0.77    inference(resolution,[],[f110,f61])).
% 3.14/0.77  fof(f61,plain,(
% 3.14/0.77    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f27])).
% 3.14/0.77  fof(f27,plain,(
% 3.14/0.77    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 3.14/0.77    inference(flattening,[],[f26])).
% 3.14/0.77  fof(f26,plain,(
% 3.14/0.77    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 3.14/0.77    inference(ennf_transformation,[],[f5])).
% 3.14/0.77  fof(f5,axiom,(
% 3.14/0.77    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
% 3.14/0.77  fof(f110,plain,(
% 3.14/0.77    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(superposition,[],[f106,f49])).
% 3.14/0.77  fof(f49,plain,(
% 3.14/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.14/0.77    inference(cnf_transformation,[],[f19])).
% 3.14/0.77  fof(f19,plain,(
% 3.14/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.14/0.77    inference(ennf_transformation,[],[f11])).
% 3.14/0.77  fof(f11,axiom,(
% 3.14/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.14/0.77  fof(f106,plain,(
% 3.14/0.77    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 3.14/0.77    inference(backward_demodulation,[],[f40,f68])).
% 3.14/0.77  fof(f68,plain,(
% 3.14/0.77    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 3.14/0.77    inference(resolution,[],[f38,f49])).
% 3.14/0.77  fof(f40,plain,(
% 3.14/0.77    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 3.14/0.77    inference(cnf_transformation,[],[f30])).
% 3.14/0.77  fof(f3080,plain,(
% 3.14/0.77    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 3.14/0.77    inference(forward_demodulation,[],[f3064,f43])).
% 3.14/0.77  fof(f43,plain,(
% 3.14/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f1])).
% 3.14/0.77  fof(f1,axiom,(
% 3.14/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.14/0.77  fof(f3064,plain,(
% 3.14/0.77    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 3.14/0.77    inference(resolution,[],[f2106,f146])).
% 3.14/0.77  fof(f146,plain,(
% 3.14/0.77    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,sK2),sK0) | r1_tarski(X0,sK0)) )),
% 3.14/0.77    inference(superposition,[],[f58,f113])).
% 3.14/0.77  fof(f113,plain,(
% 3.14/0.77    sK0 = k2_xboole_0(sK2,sK0)),
% 3.14/0.77    inference(resolution,[],[f94,f48])).
% 3.14/0.77  fof(f48,plain,(
% 3.14/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f18])).
% 3.14/0.77  fof(f18,plain,(
% 3.14/0.77    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.14/0.77    inference(ennf_transformation,[],[f3])).
% 3.14/0.77  fof(f3,axiom,(
% 3.14/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.14/0.77  fof(f94,plain,(
% 3.14/0.77    r1_tarski(sK2,sK0)),
% 3.14/0.77    inference(resolution,[],[f81,f65])).
% 3.14/0.77  fof(f65,plain,(
% 3.14/0.77    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.14/0.77    inference(equality_resolution,[],[f53])).
% 3.14/0.77  fof(f53,plain,(
% 3.14/0.77    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.14/0.77    inference(cnf_transformation,[],[f37])).
% 3.14/0.77  fof(f81,plain,(
% 3.14/0.77    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(subsumption_resolution,[],[f77,f41])).
% 3.14/0.77  fof(f77,plain,(
% 3.14/0.77    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(resolution,[],[f39,f44])).
% 3.14/0.77  fof(f44,plain,(
% 3.14/0.77    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f31])).
% 3.14/0.77  fof(f58,plain,(
% 3.14/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f21])).
% 3.14/0.77  fof(f21,plain,(
% 3.14/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.14/0.77    inference(ennf_transformation,[],[f7])).
% 3.14/0.77  fof(f7,axiom,(
% 3.14/0.77    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.14/0.77  fof(f2106,plain,(
% 3.14/0.77    ( ! [X3] : (r1_tarski(k4_xboole_0(k2_xboole_0(X3,sK1),X3),sK0)) )),
% 3.14/0.77    inference(resolution,[],[f543,f63])).
% 3.14/0.77  fof(f543,plain,(
% 3.14/0.77    ( ! [X4,X3] : (~r1_tarski(X3,k2_xboole_0(X4,sK1)) | r1_tarski(k4_xboole_0(X3,X4),sK0)) )),
% 3.14/0.77    inference(resolution,[],[f102,f57])).
% 3.14/0.77  fof(f57,plain,(
% 3.14/0.77    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.14/0.77    inference(cnf_transformation,[],[f20])).
% 3.14/0.77  fof(f20,plain,(
% 3.14/0.77    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.14/0.77    inference(ennf_transformation,[],[f6])).
% 3.14/0.77  fof(f6,axiom,(
% 3.14/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.14/0.77  fof(f102,plain,(
% 3.14/0.77    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,sK0)) )),
% 3.14/0.77    inference(resolution,[],[f90,f59])).
% 3.14/0.77  fof(f59,plain,(
% 3.14/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.14/0.77    inference(cnf_transformation,[],[f23])).
% 3.14/0.77  fof(f23,plain,(
% 3.14/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.14/0.77    inference(flattening,[],[f22])).
% 3.14/0.77  fof(f22,plain,(
% 3.14/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.14/0.77    inference(ennf_transformation,[],[f4])).
% 3.14/0.77  fof(f4,axiom,(
% 3.14/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.14/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.14/0.77  fof(f90,plain,(
% 3.14/0.77    r1_tarski(sK1,sK0)),
% 3.14/0.77    inference(resolution,[],[f73,f65])).
% 3.14/0.77  fof(f73,plain,(
% 3.14/0.77    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(subsumption_resolution,[],[f69,f41])).
% 3.14/0.77  fof(f69,plain,(
% 3.14/0.77    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.14/0.77    inference(resolution,[],[f38,f44])).
% 3.14/0.77  % SZS output end Proof for theBenchmark
% 3.14/0.77  % (15738)------------------------------
% 3.14/0.77  % (15738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.77  % (15738)Termination reason: Refutation
% 3.14/0.77  
% 3.14/0.77  % (15738)Memory used [KB]: 2942
% 3.14/0.77  % (15738)Time elapsed: 0.373 s
% 3.14/0.77  % (15738)------------------------------
% 3.14/0.77  % (15738)------------------------------
% 3.14/0.78  % (15710)Success in time 0.416 s
%------------------------------------------------------------------------------
