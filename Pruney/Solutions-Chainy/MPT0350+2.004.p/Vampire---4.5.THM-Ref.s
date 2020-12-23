%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:50 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 969 expanded)
%              Number of leaves         :   21 ( 267 expanded)
%              Depth                    :   28
%              Number of atoms          :  198 (2780 expanded)
%              Number of equality atoms :   91 ( 748 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f902,plain,(
    $false ),
    inference(subsumption_resolution,[],[f901,f111])).

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
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
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

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f77,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
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
    inference(resolution,[],[f40,f61])).

fof(f61,plain,(
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
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
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

fof(f901,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f900,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f900,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f244,f899])).

fof(f899,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f886,f268])).

fof(f268,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f124,f266])).

fof(f266,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f125,f265])).

fof(f265,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f48,f239])).

fof(f239,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f224,f233])).

fof(f233,plain,(
    sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f49,f214])).

fof(f214,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f141,f47])).

fof(f141,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f136,f59])).

fof(f136,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f135,f71])).

fof(f135,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f130,f42])).

fof(f130,plain,
    ( r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f112,f55])).

fof(f112,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f82,f106])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f224,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f223,f209])).

fof(f209,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f99,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f99,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f53,f92])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f223,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f190,f214])).

fof(f190,plain,(
    k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f53,f176])).

fof(f176,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f165,f67])).

fof(f165,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK0),sK1) ),
    inference(forward_demodulation,[],[f164,f97])).

fof(f97,plain,(
    sK1 = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f49,f92])).

fof(f164,plain,(
    k2_xboole_0(sK1,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK0),sK1) ),
    inference(forward_demodulation,[],[f162,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f162,plain,(
    k2_xboole_0(sK1,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f53,f124])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f125,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f98,f124])).

fof(f98,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f52,f92])).

fof(f124,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f120,f122])).

fof(f122,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f54,f119])).

fof(f119,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f48,f105])).

fof(f105,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f49,f93])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f120,plain,(
    k5_xboole_0(sK1,sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f54,f118])).

fof(f118,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f48,f97])).

fof(f886,plain,(
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

fof(f244,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f230,f239])).

fof(f230,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f53,f209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (29351)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (29342)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (29362)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (29346)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (29339)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (29345)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (29359)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (29356)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (29337)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (29333)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (29348)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.53  % (29338)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.53  % (29344)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.54  % (29335)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.54  % (29348)Refutation not found, incomplete strategy% (29348)------------------------------
% 1.42/0.54  % (29348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (29348)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (29348)Memory used [KB]: 6140
% 1.42/0.54  % (29348)Time elapsed: 0.003 s
% 1.42/0.54  % (29348)------------------------------
% 1.42/0.54  % (29348)------------------------------
% 1.42/0.54  % (29361)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.54  % (29336)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.55  % (29341)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (29347)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.55  % (29334)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.55  % (29353)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.55  % (29360)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.54/0.55  % (29354)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.55  % (29358)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.54/0.56  % (29350)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.56  % (29355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.56  % (29350)Refutation not found, incomplete strategy% (29350)------------------------------
% 1.54/0.56  % (29350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (29350)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (29350)Memory used [KB]: 10618
% 1.54/0.56  % (29350)Time elapsed: 0.151 s
% 1.54/0.56  % (29350)------------------------------
% 1.54/0.56  % (29350)------------------------------
% 1.54/0.56  % (29352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.56  % (29349)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.56  % (29343)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.54/0.57  % (29340)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.54/0.57  % (29357)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.58  % (29355)Refutation not found, incomplete strategy% (29355)------------------------------
% 1.54/0.58  % (29355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (29355)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (29355)Memory used [KB]: 10746
% 1.54/0.58  % (29355)Time elapsed: 0.175 s
% 1.54/0.58  % (29355)------------------------------
% 1.54/0.58  % (29355)------------------------------
% 1.54/0.58  % (29356)Refutation found. Thanks to Tanya!
% 1.54/0.58  % SZS status Theorem for theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f902,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(subsumption_resolution,[],[f901,f111])).
% 1.54/0.58  fof(f111,plain,(
% 1.54/0.58    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(backward_demodulation,[],[f86,f106])).
% 1.54/0.58  fof(f106,plain,(
% 1.54/0.58    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.54/0.58    inference(superposition,[],[f52,f93])).
% 1.54/0.58  fof(f93,plain,(
% 1.54/0.58    sK1 = k3_xboole_0(sK0,sK1)),
% 1.54/0.58    inference(superposition,[],[f92,f47])).
% 1.54/0.58  fof(f47,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f1])).
% 1.54/0.58  fof(f1,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.58  fof(f92,plain,(
% 1.54/0.58    sK1 = k3_xboole_0(sK1,sK0)),
% 1.54/0.58    inference(resolution,[],[f87,f59])).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f28])).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.58  fof(f87,plain,(
% 1.54/0.58    r1_tarski(sK1,sK0)),
% 1.54/0.58    inference(resolution,[],[f83,f71])).
% 1.54/0.58  fof(f71,plain,(
% 1.54/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(equality_resolution,[],[f62])).
% 1.54/0.58  fof(f62,plain,(
% 1.54/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.54/0.58    inference(cnf_transformation,[],[f39])).
% 1.54/0.58  fof(f39,plain,(
% 1.54/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.58    inference(rectify,[],[f36])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.58    inference(nnf_transformation,[],[f15])).
% 1.54/0.58  fof(f15,axiom,(
% 1.54/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.54/0.58  fof(f83,plain,(
% 1.54/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(subsumption_resolution,[],[f77,f42])).
% 1.54/0.58  fof(f42,plain,(
% 1.54/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f21])).
% 1.54/0.58  fof(f21,axiom,(
% 1.54/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.54/0.58  fof(f77,plain,(
% 1.54/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(resolution,[],[f40,f55])).
% 1.54/0.58  fof(f55,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f35])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.54/0.58    inference(nnf_transformation,[],[f27])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f17])).
% 1.54/0.58  fof(f17,axiom,(
% 1.54/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(cnf_transformation,[],[f34])).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f33])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f24])).
% 1.54/0.58  fof(f24,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.54/0.58    inference(negated_conjecture,[],[f23])).
% 1.54/0.58  fof(f23,conjecture,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.54/0.58  fof(f52,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.58  fof(f86,plain,(
% 1.54/0.58    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(subsumption_resolution,[],[f85,f40])).
% 1.54/0.58  fof(f85,plain,(
% 1.54/0.58    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(subsumption_resolution,[],[f84,f82])).
% 1.54/0.58  fof(f82,plain,(
% 1.54/0.58    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(forward_demodulation,[],[f76,f75])).
% 1.54/0.58  fof(f75,plain,(
% 1.54/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.54/0.58    inference(resolution,[],[f40,f61])).
% 1.54/0.58  fof(f61,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f19])).
% 1.54/0.58  fof(f19,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.54/0.58  fof(f76,plain,(
% 1.54/0.58    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(resolution,[],[f40,f60])).
% 1.54/0.58  fof(f60,plain,(
% 1.54/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f29])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f20])).
% 1.54/0.58  fof(f20,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.54/0.58  fof(f84,plain,(
% 1.54/0.58    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(superposition,[],[f81,f69])).
% 1.54/0.58  fof(f69,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f32])).
% 1.54/0.58  fof(f32,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(flattening,[],[f31])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f22])).
% 1.54/0.58  fof(f22,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.54/0.58  fof(f81,plain,(
% 1.54/0.58    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(backward_demodulation,[],[f72,f75])).
% 1.54/0.58  fof(f72,plain,(
% 1.54/0.58    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f41,f43])).
% 1.54/0.58  fof(f43,plain,(
% 1.54/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f18])).
% 1.54/0.58  fof(f18,axiom,(
% 1.54/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.54/0.58  fof(f41,plain,(
% 1.54/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.54/0.58    inference(cnf_transformation,[],[f34])).
% 1.54/0.58  fof(f901,plain,(
% 1.54/0.58    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f900,f44])).
% 1.54/0.58  fof(f44,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.54/0.58  fof(f900,plain,(
% 1.54/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.54/0.58    inference(backward_demodulation,[],[f244,f899])).
% 1.54/0.58  fof(f899,plain,(
% 1.54/0.58    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f886,f268])).
% 1.54/0.58  fof(f268,plain,(
% 1.54/0.58    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.54/0.58    inference(backward_demodulation,[],[f124,f266])).
% 1.54/0.58  fof(f266,plain,(
% 1.54/0.58    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.54/0.58    inference(backward_demodulation,[],[f125,f265])).
% 1.54/0.58  fof(f265,plain,(
% 1.54/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.54/0.58    inference(superposition,[],[f48,f239])).
% 1.54/0.58  fof(f239,plain,(
% 1.54/0.58    sK0 = k2_xboole_0(sK1,sK0)),
% 1.54/0.58    inference(backward_demodulation,[],[f224,f233])).
% 1.54/0.58  fof(f233,plain,(
% 1.54/0.58    sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(superposition,[],[f49,f214])).
% 1.54/0.58  fof(f214,plain,(
% 1.54/0.58    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(superposition,[],[f141,f47])).
% 1.54/0.58  fof(f141,plain,(
% 1.54/0.58    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 1.54/0.58    inference(resolution,[],[f136,f59])).
% 1.54/0.58  fof(f136,plain,(
% 1.54/0.58    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 1.54/0.58    inference(resolution,[],[f135,f71])).
% 1.54/0.58  fof(f135,plain,(
% 1.54/0.58    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(subsumption_resolution,[],[f130,f42])).
% 1.54/0.58  fof(f130,plain,(
% 1.54/0.58    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(resolution,[],[f112,f55])).
% 1.54/0.58  fof(f112,plain,(
% 1.54/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(backward_demodulation,[],[f82,f106])).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.54/0.58  fof(f224,plain,(
% 1.54/0.58    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f223,f209])).
% 1.54/0.58  fof(f209,plain,(
% 1.54/0.58    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(superposition,[],[f99,f67])).
% 1.54/0.58  fof(f67,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.58  fof(f99,plain,(
% 1.54/0.58    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 1.54/0.58    inference(superposition,[],[f53,f92])).
% 1.54/0.58  fof(f53,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f11])).
% 1.54/0.58  fof(f11,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.54/0.58  fof(f223,plain,(
% 1.54/0.58    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(backward_demodulation,[],[f190,f214])).
% 1.54/0.58  fof(f190,plain,(
% 1.54/0.58    k2_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(superposition,[],[f53,f176])).
% 1.54/0.58  fof(f176,plain,(
% 1.54/0.58    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(superposition,[],[f165,f67])).
% 1.54/0.58  fof(f165,plain,(
% 1.54/0.58    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK0),sK1)),
% 1.54/0.58    inference(forward_demodulation,[],[f164,f97])).
% 1.54/0.58  fof(f97,plain,(
% 1.54/0.58    sK1 = k2_xboole_0(sK1,sK1)),
% 1.54/0.58    inference(superposition,[],[f49,f92])).
% 1.54/0.58  fof(f164,plain,(
% 1.54/0.58    k2_xboole_0(sK1,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK0),sK1)),
% 1.54/0.58    inference(forward_demodulation,[],[f162,f45])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f25])).
% 1.54/0.58  fof(f25,plain,(
% 1.54/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.58    inference(rectify,[],[f3])).
% 1.54/0.58  fof(f3,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.58  fof(f162,plain,(
% 1.54/0.58    k2_xboole_0(sK1,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1))),
% 1.54/0.58    inference(superposition,[],[f53,f124])).
% 1.54/0.58  fof(f48,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.54/0.58  fof(f125,plain,(
% 1.54/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK0)),
% 1.54/0.58    inference(backward_demodulation,[],[f98,f124])).
% 1.54/0.58  fof(f98,plain,(
% 1.54/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 1.54/0.58    inference(superposition,[],[f52,f92])).
% 1.54/0.58  fof(f124,plain,(
% 1.54/0.58    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK0,sK0)),
% 1.54/0.58    inference(backward_demodulation,[],[f120,f122])).
% 1.54/0.58  fof(f122,plain,(
% 1.54/0.58    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK0,sK0)),
% 1.54/0.58    inference(superposition,[],[f54,f119])).
% 1.54/0.58  fof(f119,plain,(
% 1.54/0.58    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.54/0.58    inference(superposition,[],[f48,f105])).
% 1.54/0.58  fof(f105,plain,(
% 1.54/0.58    sK0 = k2_xboole_0(sK0,sK1)),
% 1.54/0.58    inference(superposition,[],[f49,f93])).
% 1.54/0.58  fof(f54,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.54/0.58  fof(f120,plain,(
% 1.54/0.58    k5_xboole_0(sK1,sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.54/0.58    inference(superposition,[],[f54,f118])).
% 1.54/0.58  fof(f118,plain,(
% 1.54/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.54/0.58    inference(superposition,[],[f48,f97])).
% 1.54/0.58  fof(f886,plain,(
% 1.54/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(superposition,[],[f116,f45])).
% 1.54/0.58  fof(f116,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) )),
% 1.54/0.58    inference(forward_demodulation,[],[f109,f47])).
% 1.54/0.58  fof(f109,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 1.54/0.58    inference(superposition,[],[f68,f93])).
% 1.54/0.58  fof(f68,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.54/0.58  fof(f244,plain,(
% 1.54/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(backward_demodulation,[],[f230,f239])).
% 1.54/0.58  fof(f230,plain,(
% 1.54/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(superposition,[],[f53,f209])).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (29356)------------------------------
% 1.54/0.58  % (29356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (29356)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (29356)Memory used [KB]: 2302
% 1.54/0.58  % (29356)Time elapsed: 0.170 s
% 1.54/0.58  % (29356)------------------------------
% 1.54/0.58  % (29356)------------------------------
% 1.54/0.59  % (29332)Success in time 0.228 s
%------------------------------------------------------------------------------
