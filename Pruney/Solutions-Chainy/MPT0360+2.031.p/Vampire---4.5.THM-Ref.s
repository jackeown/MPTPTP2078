%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:52 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 347 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  201 ( 797 expanded)
%              Number of equality atoms :   50 ( 227 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f711,plain,(
    $false ),
    inference(subsumption_resolution,[],[f708,f423])).

fof(f423,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f276,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f276,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f176,f220,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f220,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f159,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f159,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f52,f127])).

fof(f127,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f126,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f126,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f125,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f125,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f77,f107])).

fof(f107,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f94,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f43,f88,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f88,plain,(
    r1_tarski(sK2,sK0) ),
    inference(forward_demodulation,[],[f87,f76])).

fof(f76,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f48,f75])).

fof(f75,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f87,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f49,f46,f42,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f32])).

fof(f32,plain,
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

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f59,f74,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f52,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f176,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f160,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f160,plain,(
    r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f132,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f52,f114])).

fof(f114,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f113,f51])).

fof(f113,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f112,f50])).

fof(f112,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)) = k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[],[f77,f95])).

fof(f95,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f88,f64])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f708,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f43,f421,f69])).

fof(f421,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f44,f276,f67])).

fof(f44,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (26161)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (26144)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (26153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.53  % (26143)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.53  % (26157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.53  % (26148)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.53  % (26137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (26135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.53  % (26157)Refutation not found, incomplete strategy% (26157)------------------------------
% 1.38/0.53  % (26157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (26157)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (26157)Memory used [KB]: 10746
% 1.38/0.53  % (26157)Time elapsed: 0.086 s
% 1.38/0.53  % (26157)------------------------------
% 1.38/0.53  % (26157)------------------------------
% 1.38/0.54  % (26139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (26141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (26164)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (26145)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (26150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.54  % (26146)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.54  % (26140)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.54  % (26145)Refutation not found, incomplete strategy% (26145)------------------------------
% 1.38/0.54  % (26145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (26145)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (26145)Memory used [KB]: 10618
% 1.38/0.54  % (26145)Time elapsed: 0.132 s
% 1.38/0.54  % (26145)------------------------------
% 1.38/0.54  % (26145)------------------------------
% 1.38/0.54  % (26146)Refutation not found, incomplete strategy% (26146)------------------------------
% 1.38/0.54  % (26146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (26146)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (26146)Memory used [KB]: 10618
% 1.38/0.54  % (26146)Time elapsed: 0.135 s
% 1.38/0.54  % (26146)------------------------------
% 1.38/0.54  % (26146)------------------------------
% 1.38/0.54  % (26163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (26136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.55  % (26158)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (26152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (26162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (26152)Refutation not found, incomplete strategy% (26152)------------------------------
% 1.38/0.55  % (26152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (26152)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (26152)Memory used [KB]: 10618
% 1.38/0.55  % (26152)Time elapsed: 0.139 s
% 1.38/0.55  % (26152)------------------------------
% 1.38/0.55  % (26152)------------------------------
% 1.38/0.55  % (26138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.55  % (26155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (26156)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (26159)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (26161)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % (26142)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.56  % (26147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.56  % (26154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.56  % (26151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.57  % (26160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.57  % SZS output start Proof for theBenchmark
% 1.38/0.57  fof(f711,plain,(
% 1.38/0.57    $false),
% 1.38/0.57    inference(subsumption_resolution,[],[f708,f423])).
% 1.38/0.57  fof(f423,plain,(
% 1.38/0.57    ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f45,f276,f79])).
% 1.38/0.57  fof(f79,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.57    inference(definition_unfolding,[],[f65,f47])).
% 1.38/0.57  fof(f47,plain,(
% 1.38/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f15])).
% 1.38/0.57  fof(f15,axiom,(
% 1.38/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.38/0.57  fof(f65,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f39])).
% 1.38/0.57  fof(f39,plain,(
% 1.38/0.57    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(nnf_transformation,[],[f27])).
% 1.38/0.57  fof(f27,plain,(
% 1.38/0.57    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f19])).
% 1.38/0.57  fof(f19,axiom,(
% 1.38/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.38/0.57  fof(f276,plain,(
% 1.38/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f176,f220,f61])).
% 1.38/0.57  fof(f61,plain,(
% 1.38/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.38/0.57    inference(nnf_transformation,[],[f25])).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f14])).
% 1.38/0.57  fof(f14,axiom,(
% 1.38/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.38/0.57  fof(f220,plain,(
% 1.38/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f159,f81])).
% 1.38/0.57  fof(f81,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f71,f73])).
% 1.38/0.57  fof(f73,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f57,f68])).
% 1.38/0.57  fof(f68,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f10])).
% 1.38/0.57  fof(f10,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.57  fof(f57,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f9])).
% 1.38/0.57  fof(f9,axiom,(
% 1.38/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.57  fof(f71,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f41])).
% 1.38/0.57  fof(f41,plain,(
% 1.38/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.38/0.57    inference(flattening,[],[f40])).
% 1.38/0.57  fof(f40,plain,(
% 1.38/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.38/0.57    inference(nnf_transformation,[],[f13])).
% 1.38/0.57  fof(f13,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.38/0.57  fof(f159,plain,(
% 1.38/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(superposition,[],[f52,f127])).
% 1.38/0.57  fof(f127,plain,(
% 1.38/0.57    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.38/0.57    inference(forward_demodulation,[],[f126,f51])).
% 1.38/0.57  fof(f51,plain,(
% 1.38/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.57    inference(cnf_transformation,[],[f6])).
% 1.38/0.57  fof(f6,axiom,(
% 1.38/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.38/0.57  fof(f126,plain,(
% 1.38/0.57    k5_xboole_0(sK0,k1_xboole_0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.38/0.57    inference(forward_demodulation,[],[f125,f50])).
% 1.38/0.57  fof(f50,plain,(
% 1.38/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f7])).
% 1.38/0.57  fof(f7,axiom,(
% 1.38/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.38/0.57  fof(f125,plain,(
% 1.38/0.57    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.38/0.57    inference(superposition,[],[f77,f107])).
% 1.38/0.57  fof(f107,plain,(
% 1.38/0.57    sK1 = k3_xboole_0(sK1,sK0)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f94,f64])).
% 1.38/0.57  fof(f64,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f4])).
% 1.38/0.57  fof(f4,axiom,(
% 1.38/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.38/0.57  fof(f94,plain,(
% 1.38/0.57    r1_tarski(sK1,sK0)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f43,f88,f69])).
% 1.38/0.57  fof(f69,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f31])).
% 1.38/0.57  fof(f31,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.38/0.57    inference(flattening,[],[f30])).
% 1.38/0.57  fof(f30,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.38/0.57    inference(ennf_transformation,[],[f3])).
% 1.38/0.57  fof(f3,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.38/0.57  fof(f88,plain,(
% 1.38/0.57    r1_tarski(sK2,sK0)),
% 1.38/0.57    inference(forward_demodulation,[],[f87,f76])).
% 1.38/0.57  fof(f76,plain,(
% 1.38/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.38/0.57    inference(definition_unfolding,[],[f48,f75])).
% 1.38/0.57  fof(f75,plain,(
% 1.38/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f53,f47])).
% 1.38/0.57  fof(f53,plain,(
% 1.38/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f17])).
% 1.38/0.57  fof(f17,axiom,(
% 1.38/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.38/0.57  fof(f48,plain,(
% 1.38/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.38/0.57    inference(cnf_transformation,[],[f16])).
% 1.38/0.57  fof(f16,axiom,(
% 1.38/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.38/0.57  fof(f87,plain,(
% 1.38/0.57    r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f49,f46,f42,f67])).
% 1.38/0.57  fof(f67,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f29])).
% 1.38/0.57  fof(f29,plain,(
% 1.38/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(flattening,[],[f28])).
% 1.38/0.57  fof(f28,plain,(
% 1.38/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f18])).
% 1.38/0.57  fof(f18,axiom,(
% 1.38/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.38/0.57  fof(f42,plain,(
% 1.38/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(cnf_transformation,[],[f33])).
% 1.38/0.57  fof(f33,plain,(
% 1.38/0.57    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f32])).
% 1.38/0.57  fof(f32,plain,(
% 1.38/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f24,plain,(
% 1.38/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(flattening,[],[f23])).
% 1.38/0.57  fof(f23,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f22])).
% 1.38/0.57  fof(f22,negated_conjecture,(
% 1.38/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.38/0.57    inference(negated_conjecture,[],[f21])).
% 1.38/0.57  fof(f21,conjecture,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.38/0.57  fof(f46,plain,(
% 1.38/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.57  fof(f49,plain,(
% 1.38/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f20])).
% 1.38/0.57  fof(f20,axiom,(
% 1.38/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.38/0.57  fof(f43,plain,(
% 1.38/0.57    r1_tarski(sK1,sK2)),
% 1.38/0.57    inference(cnf_transformation,[],[f33])).
% 1.38/0.57  fof(f77,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.38/0.57    inference(definition_unfolding,[],[f59,f74,f58])).
% 1.38/0.57  fof(f58,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f2])).
% 1.38/0.57  fof(f2,axiom,(
% 1.38/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.57  fof(f74,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.38/0.57    inference(definition_unfolding,[],[f56,f73])).
% 1.38/0.57  fof(f56,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f11])).
% 1.38/0.57  fof(f11,axiom,(
% 1.38/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.38/0.57  fof(f59,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f8])).
% 1.38/0.57  fof(f8,axiom,(
% 1.38/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.38/0.57  fof(f52,plain,(
% 1.38/0.57    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f12])).
% 1.38/0.57  fof(f12,axiom,(
% 1.38/0.57    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.38/0.57  fof(f176,plain,(
% 1.38/0.57    ~v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f160,f54])).
% 1.38/0.57  fof(f54,plain,(
% 1.38/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f37])).
% 1.38/0.57  fof(f37,plain,(
% 1.38/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.38/0.57  fof(f36,plain,(
% 1.38/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f35,plain,(
% 1.38/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.57    inference(rectify,[],[f34])).
% 1.38/0.57  fof(f34,plain,(
% 1.38/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.57    inference(nnf_transformation,[],[f1])).
% 1.38/0.57  fof(f1,axiom,(
% 1.38/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.38/0.57  fof(f160,plain,(
% 1.38/0.57    r2_hidden(sK0,k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f132,f82])).
% 1.38/0.57  fof(f82,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f70,f73])).
% 1.38/0.57  fof(f70,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f41])).
% 1.38/0.57  fof(f132,plain,(
% 1.38/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK2),k1_zfmisc_1(sK0))),
% 1.38/0.57    inference(superposition,[],[f52,f114])).
% 1.38/0.57  fof(f114,plain,(
% 1.38/0.57    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))),
% 1.38/0.57    inference(forward_demodulation,[],[f113,f51])).
% 1.38/0.57  fof(f113,plain,(
% 1.38/0.57    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.38/0.57    inference(forward_demodulation,[],[f112,f50])).
% 1.38/0.57  fof(f112,plain,(
% 1.38/0.57    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)) = k5_xboole_0(sK0,k5_xboole_0(sK2,sK2))),
% 1.38/0.57    inference(superposition,[],[f77,f95])).
% 1.38/0.57  fof(f95,plain,(
% 1.38/0.57    sK2 = k3_xboole_0(sK2,sK0)),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f88,f64])).
% 1.38/0.57  fof(f45,plain,(
% 1.38/0.57    k1_xboole_0 != sK1),
% 1.38/0.57    inference(cnf_transformation,[],[f33])).
% 1.38/0.57  fof(f708,plain,(
% 1.38/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f43,f421,f69])).
% 1.38/0.57  fof(f421,plain,(
% 1.38/0.57    r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.38/0.57    inference(unit_resulting_resolution,[],[f42,f44,f276,f67])).
% 1.38/0.57  fof(f44,plain,(
% 1.38/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.38/0.57    inference(cnf_transformation,[],[f33])).
% 1.38/0.57  % SZS output end Proof for theBenchmark
% 1.38/0.57  % (26161)------------------------------
% 1.38/0.57  % (26161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (26161)Termination reason: Refutation
% 1.38/0.57  
% 1.38/0.57  % (26161)Memory used [KB]: 11385
% 1.38/0.57  % (26161)Time elapsed: 0.138 s
% 1.38/0.57  % (26161)------------------------------
% 1.38/0.57  % (26161)------------------------------
% 1.38/0.57  % (26134)Success in time 0.213 s
%------------------------------------------------------------------------------
