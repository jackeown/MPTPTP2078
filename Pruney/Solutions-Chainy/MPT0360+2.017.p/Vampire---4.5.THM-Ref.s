%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:50 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 172 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  264 ( 541 expanded)
%              Number of equality atoms :   73 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f813,plain,(
    $false ),
    inference(subsumption_resolution,[],[f802,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f802,plain,(
    k1_xboole_0 = sK1 ),
    inference(superposition,[],[f718,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f718,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f717,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f717,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(forward_demodulation,[],[f716,f102])).

fof(f102,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f716,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f687,f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ) ),
    inference(forward_demodulation,[],[f74,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f687,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f678,f358])).

fof(f358,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k5_xboole_0(sK0,sK2))
      | r1_xboole_0(X8,sK2) ) ),
    inference(forward_demodulation,[],[f357,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f357,plain,(
    ! [X8] :
      ( r1_xboole_0(X8,sK2)
      | ~ r1_tarski(X8,k5_xboole_0(sK2,sK0)) ) ),
    inference(forward_demodulation,[],[f356,f45])).

fof(f356,plain,(
    ! [X8] :
      ( r1_xboole_0(X8,k5_xboole_0(sK2,k1_xboole_0))
      | ~ r1_tarski(X8,k5_xboole_0(sK2,sK0)) ) ),
    inference(forward_demodulation,[],[f332,f44])).

fof(f332,plain,(
    ! [X8] :
      ( r1_xboole_0(X8,k5_xboole_0(sK2,k5_xboole_0(sK0,sK0)))
      | ~ r1_tarski(X8,k5_xboole_0(sK2,sK0)) ) ),
    inference(superposition,[],[f308,f105])).

fof(f105,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f53,f96])).

fof(f96,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f95,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f95,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f93,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f308,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(forward_demodulation,[],[f76,f64])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f69,f48])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f678,plain,(
    r1_tarski(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f41,f658])).

fof(f658,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f651,f46])).

fof(f651,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f552,f629])).

fof(f629,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f396,f96])).

fof(f396,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f395,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f395,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f67,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK4(X0,X1,X2))
        & r1_tarski(X2,sK4(X0,X1,X2))
        & r1_tarski(X0,sK4(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK4(X0,X1,X2))
        & r1_tarski(X2,sK4(X0,X1,X2))
        & r1_tarski(X0,sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK4(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f552,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f474,f39])).

fof(f474,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X1,k2_xboole_0(X0,X1)) ) ),
    inference(backward_demodulation,[],[f405,f170])).

fof(f170,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f155,f81])).

fof(f81,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f46,f45])).

fof(f155,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f64,f44])).

fof(f405,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) ) ),
    inference(forward_demodulation,[],[f72,f64])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f41,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29794)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (29810)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (29801)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (29811)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (29798)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (29803)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (29789)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (29790)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (29801)Refutation not found, incomplete strategy% (29801)------------------------------
% 0.21/0.53  % (29801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29801)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29801)Memory used [KB]: 10618
% 0.21/0.53  % (29801)Time elapsed: 0.130 s
% 0.21/0.53  % (29801)------------------------------
% 0.21/0.53  % (29801)------------------------------
% 0.21/0.54  % (29792)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (29793)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (29819)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (29791)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (29819)Refutation not found, incomplete strategy% (29819)------------------------------
% 0.21/0.54  % (29819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29819)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29819)Memory used [KB]: 1663
% 0.21/0.54  % (29819)Time elapsed: 0.110 s
% 0.21/0.54  % (29819)------------------------------
% 0.21/0.54  % (29819)------------------------------
% 0.21/0.54  % (29809)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (29797)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (29813)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (29815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (29800)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (29814)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (29806)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (29799)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (29818)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (29805)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (29807)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (29816)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (29804)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (29808)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.52/0.56  % (29805)Refutation not found, incomplete strategy% (29805)------------------------------
% 1.52/0.56  % (29805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (29796)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.52/0.56  % (29799)Refutation not found, incomplete strategy% (29799)------------------------------
% 1.52/0.56  % (29799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (29799)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (29799)Memory used [KB]: 10746
% 1.52/0.56  % (29799)Time elapsed: 0.160 s
% 1.52/0.56  % (29799)------------------------------
% 1.52/0.56  % (29799)------------------------------
% 1.52/0.56  % (29805)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (29805)Memory used [KB]: 10618
% 1.52/0.56  % (29805)Time elapsed: 0.150 s
% 1.52/0.56  % (29805)------------------------------
% 1.52/0.56  % (29805)------------------------------
% 1.52/0.57  % (29818)Refutation not found, incomplete strategy% (29818)------------------------------
% 1.52/0.57  % (29818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (29818)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (29818)Memory used [KB]: 10746
% 1.52/0.57  % (29818)Time elapsed: 0.159 s
% 1.52/0.57  % (29818)------------------------------
% 1.52/0.57  % (29818)------------------------------
% 1.65/0.58  % (29795)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.65/0.59  % (29817)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.65/0.60  % (29802)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.65/0.64  % (29795)Refutation found. Thanks to Tanya!
% 1.65/0.64  % SZS status Theorem for theBenchmark
% 1.65/0.64  % SZS output start Proof for theBenchmark
% 1.65/0.64  fof(f813,plain,(
% 1.65/0.64    $false),
% 1.65/0.64    inference(subsumption_resolution,[],[f802,f42])).
% 1.65/0.64  fof(f42,plain,(
% 1.65/0.64    k1_xboole_0 != sK1),
% 1.65/0.64    inference(cnf_transformation,[],[f26])).
% 1.65/0.64  fof(f26,plain,(
% 1.65/0.64    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).
% 1.65/0.64  fof(f25,plain,(
% 1.65/0.64    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.65/0.64    introduced(choice_axiom,[])).
% 1.65/0.64  fof(f19,plain,(
% 1.65/0.64    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.65/0.64    inference(flattening,[],[f18])).
% 1.65/0.64  fof(f18,plain,(
% 1.65/0.64    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.65/0.64    inference(ennf_transformation,[],[f17])).
% 1.65/0.64  fof(f17,negated_conjecture,(
% 1.65/0.64    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.65/0.64    inference(negated_conjecture,[],[f16])).
% 1.65/0.64  fof(f16,conjecture,(
% 1.65/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.65/0.64  fof(f802,plain,(
% 1.65/0.64    k1_xboole_0 = sK1),
% 1.65/0.64    inference(superposition,[],[f718,f45])).
% 1.65/0.64  fof(f45,plain,(
% 1.65/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.65/0.64    inference(cnf_transformation,[],[f8])).
% 1.65/0.64  fof(f8,axiom,(
% 1.65/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.65/0.64  fof(f718,plain,(
% 1.65/0.64    k1_xboole_0 = k5_xboole_0(sK1,k1_xboole_0)),
% 1.65/0.64    inference(forward_demodulation,[],[f717,f44])).
% 1.65/0.64  fof(f44,plain,(
% 1.65/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.65/0.64    inference(cnf_transformation,[],[f10])).
% 1.65/0.64  fof(f10,axiom,(
% 1.65/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.65/0.64  fof(f717,plain,(
% 1.65/0.64    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),
% 1.65/0.64    inference(forward_demodulation,[],[f716,f102])).
% 1.65/0.64  fof(f102,plain,(
% 1.65/0.64    sK2 = k2_xboole_0(sK1,sK2)),
% 1.65/0.64    inference(resolution,[],[f53,f40])).
% 1.65/0.64  fof(f40,plain,(
% 1.65/0.64    r1_tarski(sK1,sK2)),
% 1.65/0.64    inference(cnf_transformation,[],[f26])).
% 1.65/0.64  fof(f53,plain,(
% 1.65/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.65/0.64    inference(cnf_transformation,[],[f21])).
% 1.65/0.64  fof(f21,plain,(
% 1.65/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.65/0.64    inference(ennf_transformation,[],[f6])).
% 1.65/0.64  fof(f6,axiom,(
% 1.65/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.65/0.64  fof(f716,plain,(
% 1.65/0.64    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),
% 1.65/0.64    inference(resolution,[],[f687,f205])).
% 1.65/0.64  fof(f205,plain,(
% 1.65/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.65/0.64    inference(forward_demodulation,[],[f74,f64])).
% 1.65/0.64  fof(f64,plain,(
% 1.65/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.65/0.64    inference(cnf_transformation,[],[f9])).
% 1.65/0.64  fof(f9,axiom,(
% 1.65/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.65/0.64  fof(f74,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.64    inference(definition_unfolding,[],[f58,f48])).
% 1.65/0.64  fof(f48,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.65/0.64    inference(cnf_transformation,[],[f11])).
% 1.65/0.64  fof(f11,axiom,(
% 1.65/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.65/0.64  fof(f58,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.64    inference(cnf_transformation,[],[f30])).
% 1.65/0.64  fof(f30,plain,(
% 1.65/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.65/0.64    inference(nnf_transformation,[],[f2])).
% 1.65/0.64  fof(f2,axiom,(
% 1.65/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.65/0.64  fof(f687,plain,(
% 1.65/0.64    r1_xboole_0(sK1,sK2)),
% 1.65/0.64    inference(resolution,[],[f678,f358])).
% 1.65/0.64  fof(f358,plain,(
% 1.65/0.64    ( ! [X8] : (~r1_tarski(X8,k5_xboole_0(sK0,sK2)) | r1_xboole_0(X8,sK2)) )),
% 1.65/0.64    inference(forward_demodulation,[],[f357,f46])).
% 1.65/0.64  fof(f46,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.65/0.64    inference(cnf_transformation,[],[f1])).
% 1.65/0.64  fof(f1,axiom,(
% 1.65/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.65/0.64  fof(f357,plain,(
% 1.65/0.64    ( ! [X8] : (r1_xboole_0(X8,sK2) | ~r1_tarski(X8,k5_xboole_0(sK2,sK0))) )),
% 1.65/0.64    inference(forward_demodulation,[],[f356,f45])).
% 1.65/0.64  fof(f356,plain,(
% 1.65/0.64    ( ! [X8] : (r1_xboole_0(X8,k5_xboole_0(sK2,k1_xboole_0)) | ~r1_tarski(X8,k5_xboole_0(sK2,sK0))) )),
% 1.65/0.64    inference(forward_demodulation,[],[f332,f44])).
% 1.65/0.64  fof(f332,plain,(
% 1.65/0.64    ( ! [X8] : (r1_xboole_0(X8,k5_xboole_0(sK2,k5_xboole_0(sK0,sK0))) | ~r1_tarski(X8,k5_xboole_0(sK2,sK0))) )),
% 1.65/0.64    inference(superposition,[],[f308,f105])).
% 1.65/0.64  fof(f105,plain,(
% 1.65/0.64    sK0 = k2_xboole_0(sK2,sK0)),
% 1.65/0.64    inference(resolution,[],[f53,f96])).
% 1.65/0.64  fof(f96,plain,(
% 1.65/0.64    r1_tarski(sK2,sK0)),
% 1.65/0.64    inference(resolution,[],[f95,f80])).
% 1.65/0.64  fof(f80,plain,(
% 1.65/0.64    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.65/0.64    inference(equality_resolution,[],[f60])).
% 1.65/0.64  fof(f60,plain,(
% 1.65/0.64    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.65/0.64    inference(cnf_transformation,[],[f34])).
% 1.65/0.64  fof(f34,plain,(
% 1.65/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.65/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.65/0.64  fof(f33,plain,(
% 1.65/0.64    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.65/0.64    introduced(choice_axiom,[])).
% 1.65/0.64  fof(f32,plain,(
% 1.65/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.65/0.64    inference(rectify,[],[f31])).
% 1.65/0.64  fof(f31,plain,(
% 1.65/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.65/0.64    inference(nnf_transformation,[],[f12])).
% 1.65/0.64  fof(f12,axiom,(
% 1.65/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.65/0.64  fof(f95,plain,(
% 1.65/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.64    inference(subsumption_resolution,[],[f93,f43])).
% 1.65/0.64  fof(f43,plain,(
% 1.65/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.65/0.64    inference(cnf_transformation,[],[f15])).
% 1.65/0.64  fof(f15,axiom,(
% 1.65/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.65/0.64  fof(f93,plain,(
% 1.65/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.65/0.64    inference(resolution,[],[f49,f39])).
% 1.65/0.64  fof(f39,plain,(
% 1.65/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.64    inference(cnf_transformation,[],[f26])).
% 1.65/0.64  fof(f49,plain,(
% 1.65/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.65/0.64    inference(cnf_transformation,[],[f27])).
% 1.65/0.64  fof(f27,plain,(
% 1.65/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.65/0.64    inference(nnf_transformation,[],[f20])).
% 1.65/0.64  fof(f20,plain,(
% 1.65/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.65/0.64    inference(ennf_transformation,[],[f13])).
% 1.65/0.64  fof(f13,axiom,(
% 1.65/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.65/0.64  fof(f308,plain,(
% 1.65/0.64    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.65/0.64    inference(forward_demodulation,[],[f76,f64])).
% 1.65/0.64  fof(f76,plain,(
% 1.65/0.64    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.65/0.64    inference(definition_unfolding,[],[f69,f48])).
% 1.65/0.64  fof(f69,plain,(
% 1.65/0.64    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.65/0.64    inference(cnf_transformation,[],[f38])).
% 1.65/0.64  fof(f38,plain,(
% 1.65/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.65/0.64    inference(flattening,[],[f37])).
% 1.65/0.64  fof(f37,plain,(
% 1.65/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.65/0.64    inference(nnf_transformation,[],[f5])).
% 1.65/0.64  fof(f5,axiom,(
% 1.65/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).
% 1.65/0.64  fof(f678,plain,(
% 1.65/0.64    r1_tarski(sK1,k5_xboole_0(sK0,sK2))),
% 1.65/0.64    inference(backward_demodulation,[],[f41,f658])).
% 1.65/0.64  fof(f658,plain,(
% 1.65/0.64    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.65/0.64    inference(forward_demodulation,[],[f651,f46])).
% 1.65/0.64  fof(f651,plain,(
% 1.65/0.64    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0)),
% 1.65/0.64    inference(backward_demodulation,[],[f552,f629])).
% 1.65/0.64  fof(f629,plain,(
% 1.65/0.64    sK0 = k2_xboole_0(sK0,sK2)),
% 1.65/0.64    inference(resolution,[],[f396,f96])).
% 1.65/0.64  fof(f396,plain,(
% 1.65/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k2_xboole_0(X0,X1) = X0) )),
% 1.65/0.64    inference(subsumption_resolution,[],[f395,f77])).
% 1.65/0.64  fof(f77,plain,(
% 1.65/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/0.64    inference(equality_resolution,[],[f56])).
% 1.65/0.64  fof(f56,plain,(
% 1.65/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.65/0.64    inference(cnf_transformation,[],[f29])).
% 1.65/0.64  fof(f29,plain,(
% 1.65/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.64    inference(flattening,[],[f28])).
% 1.65/0.64  fof(f28,plain,(
% 1.65/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.64    inference(nnf_transformation,[],[f3])).
% 1.65/0.64  fof(f3,axiom,(
% 1.65/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.64  fof(f395,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.65/0.64    inference(duplicate_literal_removal,[],[f391])).
% 1.65/0.64  fof(f391,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.65/0.64    inference(resolution,[],[f67,f65])).
% 1.65/0.64  fof(f65,plain,(
% 1.65/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,sK4(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.65/0.64    inference(cnf_transformation,[],[f36])).
% 1.65/0.64  fof(f36,plain,(
% 1.65/0.64    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK4(X0,X1,X2)) & r1_tarski(X2,sK4(X0,X1,X2)) & r1_tarski(X0,sK4(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.65/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).
% 1.65/0.64  fof(f35,plain,(
% 1.65/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK4(X0,X1,X2)) & r1_tarski(X2,sK4(X0,X1,X2)) & r1_tarski(X0,sK4(X0,X1,X2))))),
% 1.65/0.64    introduced(choice_axiom,[])).
% 1.65/0.64  fof(f24,plain,(
% 1.65/0.64    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.65/0.64    inference(flattening,[],[f23])).
% 1.65/0.64  fof(f23,plain,(
% 1.65/0.64    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.65/0.64    inference(ennf_transformation,[],[f7])).
% 1.65/0.64  fof(f7,axiom,(
% 1.65/0.64    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 1.65/0.64  fof(f67,plain,(
% 1.65/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK4(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.65/0.64    inference(cnf_transformation,[],[f36])).
% 1.65/0.64  fof(f552,plain,(
% 1.65/0.64    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k2_xboole_0(sK0,sK2))),
% 1.65/0.64    inference(resolution,[],[f474,f39])).
% 1.65/0.64  fof(f474,plain,(
% 1.65/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 1.65/0.64    inference(backward_demodulation,[],[f405,f170])).
% 1.65/0.64  fof(f170,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.65/0.64    inference(forward_demodulation,[],[f155,f81])).
% 1.65/0.64  fof(f81,plain,(
% 1.65/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.65/0.64    inference(superposition,[],[f46,f45])).
% 1.65/0.64  fof(f155,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.65/0.64    inference(superposition,[],[f64,f44])).
% 1.65/0.64  fof(f405,plain,(
% 1.65/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))) )),
% 1.65/0.64    inference(forward_demodulation,[],[f72,f64])).
% 1.65/0.64  fof(f72,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.64    inference(definition_unfolding,[],[f54,f71])).
% 1.65/0.64  fof(f71,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.65/0.64    inference(definition_unfolding,[],[f47,f48])).
% 1.65/0.64  fof(f47,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.64    inference(cnf_transformation,[],[f4])).
% 1.65/0.64  fof(f4,axiom,(
% 1.65/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.64  fof(f54,plain,(
% 1.65/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.64    inference(cnf_transformation,[],[f22])).
% 1.65/0.64  fof(f22,plain,(
% 1.65/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.64    inference(ennf_transformation,[],[f14])).
% 1.65/0.64  fof(f14,axiom,(
% 1.65/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.65/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.65/0.64  fof(f41,plain,(
% 1.65/0.64    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.65/0.64    inference(cnf_transformation,[],[f26])).
% 1.65/0.64  % SZS output end Proof for theBenchmark
% 1.65/0.64  % (29795)------------------------------
% 1.65/0.64  % (29795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.64  % (29795)Termination reason: Refutation
% 1.65/0.64  
% 1.65/0.64  % (29795)Memory used [KB]: 11129
% 1.65/0.64  % (29795)Time elapsed: 0.197 s
% 1.65/0.64  % (29795)------------------------------
% 1.65/0.64  % (29795)------------------------------
% 1.65/0.64  % (29788)Success in time 0.275 s
%------------------------------------------------------------------------------
