%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:15 EST 2020

% Result     : Theorem 3.42s
% Output     : Refutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 261 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  304 ( 897 expanded)
%              Number of equality atoms :   37 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2930,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f85,f369,f961,f2875,f2929])).

fof(f2929,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f2928])).

fof(f2928,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f2927,f78])).

fof(f78,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2927,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_2 ),
    inference(resolution,[],[f2888,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f2888,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f2887,f210])).

fof(f210,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2887,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f83,f209])).

fof(f209,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2875,plain,
    ( spl4_1
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f2874])).

fof(f2874,plain,
    ( $false
    | spl4_1
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f2873,f79])).

fof(f79,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f2873,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2872,f108])).

fof(f108,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2872,plain,
    ( r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2871,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2871,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2870,f384])).

fof(f384,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f116,f213])).

fof(f213,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK0),X0) ),
    inference(resolution,[],[f205,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f205,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f197,f50])).

fof(f197,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f196,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f196,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),sK0) ),
    inference(resolution,[],[f163,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f163,plain,(
    ! [X14] :
      ( ~ r1_tarski(X14,sK1)
      | r1_tarski(X14,sK0) ) ),
    inference(resolution,[],[f69,f100])).

fof(f100,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f98,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f98,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f95,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2870,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f2863,f50])).

fof(f2863,plain,
    ( r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2))
    | ~ spl4_14 ),
    inference(resolution,[],[f2848,f247])).

fof(f247,plain,(
    ! [X12,X10,X11] :
      ( ~ r1_tarski(k4_xboole_0(X11,k4_xboole_0(X11,X10)),X12)
      | r1_tarski(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) ) ),
    inference(superposition,[],[f68,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f51,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2848,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl4_14 ),
    inference(superposition,[],[f492,f368])).

fof(f368,plain,
    ( sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl4_14
  <=> sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f492,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X1,X0),X0),X1) ),
    inference(superposition,[],[f181,f50])).

fof(f181,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(k2_xboole_0(X6,X7),X6),X7) ),
    inference(resolution,[],[f67,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f961,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f953])).

fof(f953,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f683,f364])).

fof(f364,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl4_13
  <=> r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f683,plain,(
    ! [X4] : r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,X4)),sK0) ),
    inference(forward_demodulation,[],[f676,f50])).

fof(f676,plain,(
    ! [X4] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,X4),sK2),sK0) ),
    inference(superposition,[],[f520,f110])).

fof(f110,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(resolution,[],[f57,f48])).

fof(f520,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f491,f68])).

fof(f491,plain,(
    ! [X16] : r1_tarski(k4_xboole_0(k2_xboole_0(X16,sK2),X16),sK0) ),
    inference(resolution,[],[f181,f164])).

fof(f164,plain,(
    ! [X15] :
      ( ~ r1_tarski(X15,sK2)
      | r1_tarski(X15,sK0) ) ),
    inference(resolution,[],[f69,f101])).

fof(f101,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f99,f75])).

fof(f99,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f96,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f53,f42])).

fof(f369,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f359,f81,f366,f362])).

fof(f359,plain,
    ( sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f342,f61])).

fof(f342,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f341,f68])).

fof(f341,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f328,f210])).

fof(f328,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f82,f209])).

fof(f82,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f85,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f43,f81,f77])).

fof(f43,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f44,f81,f77])).

fof(f44,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.19/0.52  % (8074)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.19/0.52  % (8095)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.19/0.53  % (8087)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.54  % (8073)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.54  % (8070)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.54  % (8069)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (8072)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (8071)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.54  % (8077)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.55  % (8086)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  % (8085)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (8089)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.55  % (8094)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.55  % (8093)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.55  % (8081)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.55  % (8096)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.56  % (8080)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.56  % (8082)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.56  % (8079)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.56  % (8091)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.56  % (8088)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.56  % (8099)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.56  % (8097)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.56  % (8092)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.56  % (8075)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.57  % (8084)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.57  % (8076)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.58  % (8090)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.59  % (8083)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.60  % (8098)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.57/0.73  % (8072)Refutation not found, incomplete strategy% (8072)------------------------------
% 2.57/0.73  % (8072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.57/0.73  % (8072)Termination reason: Refutation not found, incomplete strategy
% 2.57/0.73  
% 2.57/0.73  % (8072)Memory used [KB]: 6140
% 2.57/0.73  % (8072)Time elapsed: 0.317 s
% 2.57/0.73  % (8072)------------------------------
% 2.57/0.73  % (8072)------------------------------
% 3.42/0.81  % (8094)Time limit reached!
% 3.42/0.81  % (8094)------------------------------
% 3.42/0.81  % (8094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.81  % (8094)Termination reason: Time limit
% 3.42/0.81  
% 3.42/0.81  % (8094)Memory used [KB]: 12409
% 3.42/0.81  % (8094)Time elapsed: 0.407 s
% 3.42/0.81  % (8094)------------------------------
% 3.42/0.81  % (8094)------------------------------
% 3.42/0.82  % (8075)Refutation found. Thanks to Tanya!
% 3.42/0.82  % SZS status Theorem for theBenchmark
% 3.42/0.82  % (8071)Time limit reached!
% 3.42/0.82  % (8071)------------------------------
% 3.42/0.82  % (8071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.82  % (8071)Termination reason: Time limit
% 3.42/0.82  
% 3.42/0.82  % (8071)Memory used [KB]: 6652
% 3.42/0.82  % (8071)Time elapsed: 0.414 s
% 3.42/0.82  % (8071)------------------------------
% 3.42/0.82  % (8071)------------------------------
% 3.67/0.84  % SZS output start Proof for theBenchmark
% 3.67/0.84  fof(f2930,plain,(
% 3.67/0.84    $false),
% 3.67/0.84    inference(avatar_sat_refutation,[],[f84,f85,f369,f961,f2875,f2929])).
% 3.67/0.84  fof(f2929,plain,(
% 3.67/0.84    ~spl4_1 | spl4_2),
% 3.67/0.84    inference(avatar_contradiction_clause,[],[f2928])).
% 3.67/0.84  fof(f2928,plain,(
% 3.67/0.84    $false | (~spl4_1 | spl4_2)),
% 3.67/0.84    inference(subsumption_resolution,[],[f2927,f78])).
% 3.67/0.84  fof(f78,plain,(
% 3.67/0.84    r1_tarski(sK1,sK2) | ~spl4_1),
% 3.67/0.84    inference(avatar_component_clause,[],[f77])).
% 3.67/0.84  fof(f77,plain,(
% 3.67/0.84    spl4_1 <=> r1_tarski(sK1,sK2)),
% 3.67/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.67/0.84  fof(f2927,plain,(
% 3.67/0.84    ~r1_tarski(sK1,sK2) | spl4_2),
% 3.67/0.84    inference(resolution,[],[f2888,f66])).
% 3.67/0.84  fof(f66,plain,(
% 3.67/0.84    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f24])).
% 3.67/0.84  fof(f24,plain,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.67/0.84    inference(ennf_transformation,[],[f8])).
% 3.67/0.84  fof(f8,axiom,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 3.67/0.84  fof(f2888,plain,(
% 3.67/0.84    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 3.67/0.84    inference(forward_demodulation,[],[f2887,f210])).
% 3.67/0.84  fof(f210,plain,(
% 3.67/0.84    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 3.67/0.84    inference(resolution,[],[f58,f42])).
% 3.67/0.84  fof(f42,plain,(
% 3.67/0.84    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(cnf_transformation,[],[f33])).
% 3.67/0.84  fof(f33,plain,(
% 3.67/0.84    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32,f31])).
% 3.67/0.84  fof(f31,plain,(
% 3.67/0.84    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 3.67/0.84    introduced(choice_axiom,[])).
% 3.67/0.84  fof(f32,plain,(
% 3.67/0.84    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 3.67/0.84    introduced(choice_axiom,[])).
% 3.67/0.84  fof(f30,plain,(
% 3.67/0.84    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/0.84    inference(flattening,[],[f29])).
% 3.67/0.84  fof(f29,plain,(
% 3.67/0.84    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/0.84    inference(nnf_transformation,[],[f20])).
% 3.67/0.84  fof(f20,plain,(
% 3.67/0.84    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/0.84    inference(ennf_transformation,[],[f19])).
% 3.67/0.84  fof(f19,negated_conjecture,(
% 3.67/0.84    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.67/0.84    inference(negated_conjecture,[],[f18])).
% 3.67/0.84  fof(f18,conjecture,(
% 3.67/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 3.67/0.84  fof(f58,plain,(
% 3.67/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f23])).
% 3.67/0.84  fof(f23,plain,(
% 3.67/0.84    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.67/0.84    inference(ennf_transformation,[],[f16])).
% 3.67/0.84  fof(f16,axiom,(
% 3.67/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.67/0.84  fof(f2887,plain,(
% 3.67/0.84    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 3.67/0.84    inference(forward_demodulation,[],[f83,f209])).
% 3.67/0.84  fof(f209,plain,(
% 3.67/0.84    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 3.67/0.84    inference(resolution,[],[f58,f41])).
% 3.67/0.84  fof(f41,plain,(
% 3.67/0.84    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(cnf_transformation,[],[f33])).
% 3.67/0.84  fof(f83,plain,(
% 3.67/0.84    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_2),
% 3.67/0.84    inference(avatar_component_clause,[],[f81])).
% 3.67/0.84  fof(f81,plain,(
% 3.67/0.84    spl4_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.67/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.67/0.84  fof(f2875,plain,(
% 3.67/0.84    spl4_1 | ~spl4_14),
% 3.67/0.84    inference(avatar_contradiction_clause,[],[f2874])).
% 3.67/0.84  fof(f2874,plain,(
% 3.67/0.84    $false | (spl4_1 | ~spl4_14)),
% 3.67/0.84    inference(subsumption_resolution,[],[f2873,f79])).
% 3.67/0.84  fof(f79,plain,(
% 3.67/0.84    ~r1_tarski(sK1,sK2) | spl4_1),
% 3.67/0.84    inference(avatar_component_clause,[],[f77])).
% 3.67/0.84  fof(f2873,plain,(
% 3.67/0.84    r1_tarski(sK1,sK2) | ~spl4_14),
% 3.67/0.84    inference(forward_demodulation,[],[f2872,f108])).
% 3.67/0.84  fof(f108,plain,(
% 3.67/0.84    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.67/0.84    inference(resolution,[],[f57,f46])).
% 3.67/0.84  fof(f46,plain,(
% 3.67/0.84    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f7])).
% 3.67/0.84  fof(f7,axiom,(
% 3.67/0.84    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.67/0.84  fof(f57,plain,(
% 3.67/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.67/0.84    inference(cnf_transformation,[],[f22])).
% 3.67/0.84  fof(f22,plain,(
% 3.67/0.84    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.67/0.84    inference(ennf_transformation,[],[f5])).
% 3.67/0.84  fof(f5,axiom,(
% 3.67/0.84    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.67/0.84  fof(f2872,plain,(
% 3.67/0.84    r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2)) | ~spl4_14),
% 3.67/0.84    inference(forward_demodulation,[],[f2871,f50])).
% 3.67/0.84  fof(f50,plain,(
% 3.67/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f1])).
% 3.67/0.84  fof(f1,axiom,(
% 3.67/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.67/0.84  fof(f2871,plain,(
% 3.67/0.84    r1_tarski(sK1,k2_xboole_0(sK2,k1_xboole_0)) | ~spl4_14),
% 3.67/0.84    inference(forward_demodulation,[],[f2870,f384])).
% 3.67/0.84  fof(f384,plain,(
% 3.67/0.84    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 3.67/0.84    inference(resolution,[],[f116,f213])).
% 3.67/0.84  fof(f213,plain,(
% 3.67/0.84    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK0),X0)) )),
% 3.67/0.84    inference(resolution,[],[f205,f67])).
% 3.67/0.84  fof(f67,plain,(
% 3.67/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f25])).
% 3.67/0.84  fof(f25,plain,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.67/0.84    inference(ennf_transformation,[],[f10])).
% 3.67/0.84  fof(f10,axiom,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.67/0.84  fof(f205,plain,(
% 3.67/0.84    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(sK0,X0))) )),
% 3.67/0.84    inference(superposition,[],[f197,f50])).
% 3.67/0.84  fof(f197,plain,(
% 3.67/0.84    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(X0,sK0))) )),
% 3.67/0.84    inference(resolution,[],[f196,f68])).
% 3.67/0.84  fof(f68,plain,(
% 3.67/0.84    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.67/0.84    inference(cnf_transformation,[],[f26])).
% 3.67/0.84  fof(f26,plain,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.67/0.84    inference(ennf_transformation,[],[f11])).
% 3.67/0.84  fof(f11,axiom,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.67/0.84  fof(f196,plain,(
% 3.67/0.84    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),sK0)) )),
% 3.67/0.84    inference(resolution,[],[f163,f48])).
% 3.67/0.84  fof(f48,plain,(
% 3.67/0.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f9])).
% 3.67/0.84  fof(f9,axiom,(
% 3.67/0.84    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.67/0.84  fof(f163,plain,(
% 3.67/0.84    ( ! [X14] : (~r1_tarski(X14,sK1) | r1_tarski(X14,sK0)) )),
% 3.67/0.84    inference(resolution,[],[f69,f100])).
% 3.67/0.84  fof(f100,plain,(
% 3.67/0.84    r1_tarski(sK1,sK0)),
% 3.67/0.84    inference(resolution,[],[f98,f75])).
% 3.67/0.84  fof(f75,plain,(
% 3.67/0.84    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 3.67/0.84    inference(equality_resolution,[],[f62])).
% 3.67/0.84  fof(f62,plain,(
% 3.67/0.84    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.67/0.84    inference(cnf_transformation,[],[f40])).
% 3.67/0.84  fof(f40,plain,(
% 3.67/0.84    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.67/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 3.67/0.84  fof(f39,plain,(
% 3.67/0.84    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.67/0.84    introduced(choice_axiom,[])).
% 3.67/0.84  fof(f38,plain,(
% 3.67/0.84    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.67/0.84    inference(rectify,[],[f37])).
% 3.67/0.84  fof(f37,plain,(
% 3.67/0.84    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.67/0.84    inference(nnf_transformation,[],[f14])).
% 3.67/0.84  fof(f14,axiom,(
% 3.67/0.84    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.67/0.84  fof(f98,plain,(
% 3.67/0.84    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(subsumption_resolution,[],[f95,f45])).
% 3.67/0.84  fof(f45,plain,(
% 3.67/0.84    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.67/0.84    inference(cnf_transformation,[],[f17])).
% 3.67/0.84  fof(f17,axiom,(
% 3.67/0.84    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.67/0.84  fof(f95,plain,(
% 3.67/0.84    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(resolution,[],[f53,f41])).
% 3.67/0.84  fof(f53,plain,(
% 3.67/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f34])).
% 3.67/0.84  fof(f34,plain,(
% 3.67/0.84    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.67/0.84    inference(nnf_transformation,[],[f21])).
% 3.67/0.84  fof(f21,plain,(
% 3.67/0.84    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.67/0.84    inference(ennf_transformation,[],[f15])).
% 3.67/0.84  fof(f15,axiom,(
% 3.67/0.84    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 3.67/0.84  fof(f69,plain,(
% 3.67/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f28])).
% 3.67/0.84  fof(f28,plain,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.67/0.84    inference(flattening,[],[f27])).
% 3.67/0.84  fof(f27,plain,(
% 3.67/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.67/0.84    inference(ennf_transformation,[],[f6])).
% 3.67/0.84  fof(f6,axiom,(
% 3.67/0.84    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.67/0.84  fof(f116,plain,(
% 3.67/0.84    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.67/0.84    inference(resolution,[],[f61,f46])).
% 3.67/0.84  fof(f61,plain,(
% 3.67/0.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f36])).
% 3.67/0.84  fof(f36,plain,(
% 3.67/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.84    inference(flattening,[],[f35])).
% 3.67/0.84  fof(f35,plain,(
% 3.67/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.84    inference(nnf_transformation,[],[f3])).
% 3.67/0.84  fof(f3,axiom,(
% 3.67/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.67/0.84  fof(f2870,plain,(
% 3.67/0.84    r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl4_14),
% 3.67/0.84    inference(forward_demodulation,[],[f2863,f50])).
% 3.67/0.84  fof(f2863,plain,(
% 3.67/0.84    r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)) | ~spl4_14),
% 3.67/0.84    inference(resolution,[],[f2848,f247])).
% 3.67/0.84  fof(f247,plain,(
% 3.67/0.84    ( ! [X12,X10,X11] : (~r1_tarski(k4_xboole_0(X11,k4_xboole_0(X11,X10)),X12) | r1_tarski(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12))) )),
% 3.67/0.84    inference(superposition,[],[f68,f71])).
% 3.67/0.84  fof(f71,plain,(
% 3.67/0.84    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.67/0.84    inference(definition_unfolding,[],[f49,f51,f51])).
% 3.67/0.84  fof(f51,plain,(
% 3.67/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.67/0.84    inference(cnf_transformation,[],[f12])).
% 3.67/0.84  fof(f12,axiom,(
% 3.67/0.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.67/0.84  fof(f49,plain,(
% 3.67/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.67/0.84    inference(cnf_transformation,[],[f2])).
% 3.67/0.84  fof(f2,axiom,(
% 3.67/0.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.67/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.67/0.84  fof(f2848,plain,(
% 3.67/0.84    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl4_14),
% 3.67/0.84    inference(superposition,[],[f492,f368])).
% 3.67/0.84  fof(f368,plain,(
% 3.67/0.84    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl4_14),
% 3.67/0.84    inference(avatar_component_clause,[],[f366])).
% 3.67/0.84  fof(f366,plain,(
% 3.67/0.84    spl4_14 <=> sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 3.67/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.67/0.84  fof(f492,plain,(
% 3.67/0.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X0),X0),X1)) )),
% 3.67/0.84    inference(superposition,[],[f181,f50])).
% 3.67/0.84  fof(f181,plain,(
% 3.67/0.84    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(k2_xboole_0(X6,X7),X6),X7)) )),
% 3.67/0.84    inference(resolution,[],[f67,f72])).
% 3.67/0.84  fof(f72,plain,(
% 3.67/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.67/0.84    inference(equality_resolution,[],[f60])).
% 3.67/0.84  fof(f60,plain,(
% 3.67/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.67/0.84    inference(cnf_transformation,[],[f36])).
% 3.67/0.84  fof(f961,plain,(
% 3.67/0.84    spl4_13),
% 3.67/0.84    inference(avatar_contradiction_clause,[],[f953])).
% 3.67/0.84  fof(f953,plain,(
% 3.67/0.84    $false | spl4_13),
% 3.67/0.84    inference(resolution,[],[f683,f364])).
% 3.67/0.84  fof(f364,plain,(
% 3.67/0.84    ~r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0) | spl4_13),
% 3.67/0.84    inference(avatar_component_clause,[],[f362])).
% 3.67/0.84  fof(f362,plain,(
% 3.67/0.84    spl4_13 <=> r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0)),
% 3.67/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.67/0.84  fof(f683,plain,(
% 3.67/0.84    ( ! [X4] : (r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,X4)),sK0)) )),
% 3.67/0.84    inference(forward_demodulation,[],[f676,f50])).
% 3.67/0.84  fof(f676,plain,(
% 3.67/0.84    ( ! [X4] : (r1_tarski(k2_xboole_0(k4_xboole_0(sK0,X4),sK2),sK0)) )),
% 3.67/0.84    inference(superposition,[],[f520,f110])).
% 3.67/0.84  fof(f110,plain,(
% 3.67/0.84    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 3.67/0.84    inference(resolution,[],[f57,f48])).
% 3.67/0.84  fof(f520,plain,(
% 3.67/0.84    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK0))) )),
% 3.67/0.84    inference(resolution,[],[f491,f68])).
% 3.67/0.84  fof(f491,plain,(
% 3.67/0.84    ( ! [X16] : (r1_tarski(k4_xboole_0(k2_xboole_0(X16,sK2),X16),sK0)) )),
% 3.67/0.84    inference(resolution,[],[f181,f164])).
% 3.67/0.84  fof(f164,plain,(
% 3.67/0.84    ( ! [X15] : (~r1_tarski(X15,sK2) | r1_tarski(X15,sK0)) )),
% 3.67/0.84    inference(resolution,[],[f69,f101])).
% 3.67/0.84  fof(f101,plain,(
% 3.67/0.84    r1_tarski(sK2,sK0)),
% 3.67/0.84    inference(resolution,[],[f99,f75])).
% 3.67/0.84  fof(f99,plain,(
% 3.67/0.84    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(subsumption_resolution,[],[f96,f45])).
% 3.67/0.84  fof(f96,plain,(
% 3.67/0.84    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 3.67/0.84    inference(resolution,[],[f53,f42])).
% 3.67/0.84  fof(f369,plain,(
% 3.67/0.84    ~spl4_13 | spl4_14 | ~spl4_2),
% 3.67/0.84    inference(avatar_split_clause,[],[f359,f81,f366,f362])).
% 3.67/0.84  fof(f359,plain,(
% 3.67/0.84    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0) | ~spl4_2),
% 3.67/0.84    inference(resolution,[],[f342,f61])).
% 3.67/0.84  fof(f342,plain,(
% 3.67/0.84    r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl4_2),
% 3.67/0.84    inference(resolution,[],[f341,f68])).
% 3.67/0.84  fof(f341,plain,(
% 3.67/0.84    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 3.67/0.84    inference(backward_demodulation,[],[f328,f210])).
% 3.67/0.84  fof(f328,plain,(
% 3.67/0.84    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 3.67/0.84    inference(backward_demodulation,[],[f82,f209])).
% 3.67/0.84  fof(f82,plain,(
% 3.67/0.84    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_2),
% 3.67/0.84    inference(avatar_component_clause,[],[f81])).
% 3.67/0.84  fof(f85,plain,(
% 3.67/0.84    spl4_1 | spl4_2),
% 3.67/0.84    inference(avatar_split_clause,[],[f43,f81,f77])).
% 3.67/0.84  fof(f43,plain,(
% 3.67/0.84    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 3.67/0.84    inference(cnf_transformation,[],[f33])).
% 3.67/0.84  fof(f84,plain,(
% 3.67/0.84    ~spl4_1 | ~spl4_2),
% 3.67/0.84    inference(avatar_split_clause,[],[f44,f81,f77])).
% 3.67/0.84  fof(f44,plain,(
% 3.67/0.84    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 3.67/0.84    inference(cnf_transformation,[],[f33])).
% 3.67/0.84  % SZS output end Proof for theBenchmark
% 3.67/0.85  % (8075)------------------------------
% 3.67/0.85  % (8075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.85  % (8075)Termination reason: Refutation
% 3.67/0.85  
% 3.67/0.85  % (8075)Memory used [KB]: 12665
% 3.67/0.85  % (8075)Time elapsed: 0.409 s
% 3.67/0.85  % (8075)------------------------------
% 3.67/0.85  % (8075)------------------------------
% 3.67/0.85  % (8067)Success in time 0.484 s
%------------------------------------------------------------------------------
