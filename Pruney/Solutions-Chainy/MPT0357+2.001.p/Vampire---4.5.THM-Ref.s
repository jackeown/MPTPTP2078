%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:26 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 198 expanded)
%              Number of leaves         :   20 (  64 expanded)
%              Depth                    :   20
%              Number of atoms          :  183 ( 503 expanded)
%              Number of equality atoms :   59 ( 131 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f232,f76])).

fof(f76,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f35,f73])).

fof(f73,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
        & r1_tarski(k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
      & r1_tarski(k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f35,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f232,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f39,f197])).

fof(f197,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f63,f151])).

fof(f151,plain,(
    sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(forward_demodulation,[],[f150,f93])).

fof(f93,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f87,f60])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f87,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0)) ),
    inference(superposition,[],[f64,f80])).

fof(f80,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f78,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f72,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f69,f36])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f69,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f59,f59])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f150,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(forward_demodulation,[],[f149,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f43,f43])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f149,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) ),
    inference(forward_demodulation,[],[f136,f64])).

fof(f136,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f64,f125])).

fof(f125,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f124,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f124,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f118,f104])).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK2,X0) ),
    inference(forward_demodulation,[],[f97,f38])).

fof(f97,plain,(
    ! [X0] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0) ),
    inference(superposition,[],[f65,f84])).

fof(f84,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f82,f57])).

fof(f82,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f77,f67])).

fof(f77,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f74,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f33,f47])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f58,f44,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f118,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f62,f81])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f34,f68])).

fof(f68,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f51])).

fof(f34,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f44,f44])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:45:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (11733)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (11720)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (11725)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (11725)Refutation not found, incomplete strategy% (11725)------------------------------
% 0.21/0.51  % (11725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11716)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (11710)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (11725)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11725)Memory used [KB]: 6140
% 0.21/0.52  % (11725)Time elapsed: 0.058 s
% 0.21/0.52  % (11725)------------------------------
% 0.21/0.52  % (11725)------------------------------
% 0.21/0.52  % (11719)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (11710)Refutation not found, incomplete strategy% (11710)------------------------------
% 0.21/0.52  % (11710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11710)Memory used [KB]: 1663
% 0.21/0.52  % (11720)Refutation not found, incomplete strategy% (11720)------------------------------
% 0.21/0.52  % (11720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11720)Memory used [KB]: 10618
% 0.21/0.52  % (11720)Time elapsed: 0.059 s
% 0.21/0.52  % (11720)------------------------------
% 0.21/0.52  % (11720)------------------------------
% 0.21/0.52  % (11712)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (11735)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (11718)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (11715)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (11719)Refutation not found, incomplete strategy% (11719)------------------------------
% 0.21/0.52  % (11719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11713)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (11719)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11719)Memory used [KB]: 10618
% 0.21/0.52  % (11719)Time elapsed: 0.098 s
% 0.21/0.52  % (11719)------------------------------
% 0.21/0.52  % (11719)------------------------------
% 0.21/0.53  % (11714)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (11714)Refutation not found, incomplete strategy% (11714)------------------------------
% 0.21/0.53  % (11714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11714)Memory used [KB]: 6268
% 0.21/0.53  % (11714)Time elapsed: 0.106 s
% 0.21/0.53  % (11714)------------------------------
% 0.21/0.53  % (11714)------------------------------
% 0.21/0.53  % (11727)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (11721)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (11721)Refutation not found, incomplete strategy% (11721)------------------------------
% 0.21/0.53  % (11721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11721)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11721)Memory used [KB]: 10618
% 0.21/0.53  % (11721)Time elapsed: 0.122 s
% 0.21/0.53  % (11721)------------------------------
% 0.21/0.53  % (11721)------------------------------
% 0.21/0.54  % (11727)Refutation not found, incomplete strategy% (11727)------------------------------
% 0.21/0.54  % (11727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 1.36/0.54  % (11727)Memory used [KB]: 10618
% 1.36/0.54  % (11727)Time elapsed: 0.119 s
% 1.36/0.54  % (11727)------------------------------
% 1.36/0.54  % (11727)------------------------------
% 1.36/0.54  % (11728)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.54  % (11710)Time elapsed: 0.095 s
% 1.36/0.54  % (11710)------------------------------
% 1.36/0.54  % (11710)------------------------------
% 1.36/0.54  % (11739)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (11736)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (11711)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (11738)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (11732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (11732)Refutation not found, incomplete strategy% (11732)------------------------------
% 1.36/0.54  % (11732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (11732)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (11732)Memory used [KB]: 10746
% 1.36/0.54  % (11732)Time elapsed: 0.129 s
% 1.36/0.54  % (11732)------------------------------
% 1.36/0.54  % (11732)------------------------------
% 1.36/0.55  % (11737)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (11731)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (11717)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (11718)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f244,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(subsumption_resolution,[],[f232,f76])).
% 1.36/0.55  fof(f76,plain,(
% 1.36/0.55    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 1.36/0.55    inference(backward_demodulation,[],[f35,f73])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(resolution,[],[f33,f51])).
% 1.36/0.55  fof(f51,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,axiom,(
% 1.36/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.55    inference(flattening,[],[f19])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 1.36/0.55    inference(negated_conjecture,[],[f17])).
% 1.36/0.55  fof(f17,conjecture,(
% 1.36/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  fof(f232,plain,(
% 1.36/0.55    r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 1.36/0.55    inference(superposition,[],[f39,f197])).
% 1.36/0.55  fof(f197,plain,(
% 1.36/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK1,sK2)),
% 1.36/0.55    inference(superposition,[],[f63,f151])).
% 1.36/0.55  fof(f151,plain,(
% 1.36/0.55    sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f150,f93])).
% 1.36/0.55  fof(f93,plain,(
% 1.36/0.55    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.36/0.55    inference(forward_demodulation,[],[f87,f60])).
% 1.36/0.55  fof(f60,plain,(
% 1.36/0.55    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.36/0.55    inference(definition_unfolding,[],[f37,f59])).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f42,f43])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.36/0.55  fof(f87,plain,(
% 1.36/0.55    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0))),
% 1.36/0.55    inference(superposition,[],[f64,f80])).
% 1.36/0.55  fof(f80,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.36/0.55    inference(resolution,[],[f78,f57])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.36/0.55    inference(nnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.36/0.55  fof(f78,plain,(
% 1.36/0.55    r1_tarski(sK1,sK0)),
% 1.36/0.55    inference(resolution,[],[f72,f67])).
% 1.36/0.55  fof(f67,plain,(
% 1.36/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.36/0.55    inference(equality_resolution,[],[f52])).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.36/0.55    inference(rectify,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.36/0.55    inference(nnf_transformation,[],[f12])).
% 1.36/0.55  fof(f12,axiom,(
% 1.36/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.36/0.55  fof(f72,plain,(
% 1.36/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(subsumption_resolution,[],[f69,f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,axiom,(
% 1.36/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(resolution,[],[f32,f47])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.36/0.55    inference(nnf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f46,f59,f59])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.36/0.55  fof(f150,plain,(
% 1.36/0.55    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f149,f61])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f40,f43,f43])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.36/0.55  fof(f149,plain,(
% 1.36/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f136,f64])).
% 1.36/0.55  fof(f136,plain,(
% 1.36/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1)))),
% 1.36/0.55    inference(superposition,[],[f64,f125])).
% 1.36/0.55  fof(f125,plain,(
% 1.36/0.55    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1)),
% 1.36/0.55    inference(forward_demodulation,[],[f124,f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.36/0.55  fof(f124,plain,(
% 1.36/0.55    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK2,sK1)),
% 1.36/0.55    inference(forward_demodulation,[],[f118,f104])).
% 1.36/0.55  fof(f104,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK2,X0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f97,f38])).
% 1.36/0.55  fof(f97,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0)) )),
% 1.36/0.55    inference(superposition,[],[f65,f84])).
% 1.36/0.55  fof(f84,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 1.36/0.55    inference(resolution,[],[f82,f57])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    r1_tarski(sK2,sK0)),
% 1.36/0.55    inference(resolution,[],[f77,f67])).
% 1.36/0.55  fof(f77,plain,(
% 1.36/0.55    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(subsumption_resolution,[],[f74,f36])).
% 1.36/0.55  fof(f74,plain,(
% 1.36/0.55    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.36/0.55    inference(resolution,[],[f33,f47])).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f58,f44,f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.36/0.55  fof(f118,plain,(
% 1.36/0.55    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 1.36/0.55    inference(superposition,[],[f62,f81])).
% 1.36/0.55  fof(f81,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.36/0.55    inference(resolution,[],[f71,f57])).
% 1.36/0.55  fof(f71,plain,(
% 1.36/0.55    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 1.36/0.55    inference(backward_demodulation,[],[f34,f68])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.36/0.55    inference(resolution,[],[f32,f51])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f41,f44,f44])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.55  fof(f63,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f45,f59])).
% 1.36/0.55  fof(f45,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (11718)------------------------------
% 1.36/0.55  % (11718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (11718)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (11718)Memory used [KB]: 10874
% 1.36/0.55  % (11718)Time elapsed: 0.128 s
% 1.36/0.55  % (11718)------------------------------
% 1.36/0.55  % (11718)------------------------------
% 1.36/0.55  % (11709)Success in time 0.178 s
%------------------------------------------------------------------------------
