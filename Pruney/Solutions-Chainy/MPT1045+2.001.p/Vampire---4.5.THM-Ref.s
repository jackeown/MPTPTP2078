%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 (1515 expanded)
%              Number of leaves         :   22 ( 380 expanded)
%              Depth                    :   36
%              Number of atoms          :  376 (6351 expanded)
%              Number of equality atoms :  166 (3015 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f156,f408])).

fof(f408,plain,(
    ! [X1] : k1_xboole_0 = X1 ),
    inference(trivial_inequality_removal,[],[f326])).

fof(f326,plain,(
    ! [X1] :
      ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f208,f311])).

fof(f311,plain,(
    ! [X0] :
      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f305,f204])).

fof(f204,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f202])).

fof(f202,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f193,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f112,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f87,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f193,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f180,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f180,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f56,f178])).

fof(f178,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( k5_partfun1(sK0,sK1,sK2) != k5_partfun1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f135,f169])).

fof(f169,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f168,f54])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f165,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

fof(f165,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f164,f56])).

fof(f164,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ v1_funct_2(sK2,sK0,X4)
      | ~ v1_funct_1(sK2)
      | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f159,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f159,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X1] :
      ( k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,X1)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f147,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f147,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f99,f56])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | k5_partfun1(X0,X1,X2) = k2_enumset1(X2,X2,X2,X2)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f59,f96])).

fof(f96,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f82,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k5_partfun1(X0,X1,X2) != k1_tarski(X2) )
        & ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f135,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f97,f133])).

fof(f133,plain,(
    sK2 = k3_partfun1(sK2,sK0,sK1) ),
    inference(resolution,[],[f128,f54])).

fof(f128,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k3_partfun1(sK2,sK0,sK1) ),
    inference(resolution,[],[f61,f56])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(f97,plain,(
    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f58,f96])).

fof(f58,plain,(
    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f305,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k1_xboole_0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f291,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(k1_xboole_0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f284,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f284,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(k1_xboole_0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f269,f71])).

fof(f269,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f268,f71])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X0] :
      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f261,f125])).

fof(f125,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f124,f89])).

fof(f89,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f124,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f76,f88])).

fof(f88,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f261,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f260,f202])).

fof(f260,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k1_xboole_0)
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f259,f105])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f259,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,X0))
      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f258,f192])).

fof(f192,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f57,f178])).

fof(f57,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f46])).

fof(f258,plain,(
    ! [X0] :
      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f257,f192])).

fof(f257,plain,(
    ! [X0] :
      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f256,f178])).

fof(f256,plain,(
    ! [X0] :
      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(sK0,sK1,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f255,f202])).

fof(f255,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f254,f202])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ v1_funct_1(sK2)
      | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f253,f202])).

fof(f253,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
      | ~ v1_funct_1(sK2)
      | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f166,f192])).

fof(f166,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,sK0,X0)
      | ~ v1_funct_1(sK2)
      | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,X0)) ) ),
    inference(resolution,[],[f164,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f208,plain,(
    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f207,f192])).

fof(f207,plain,(
    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f182,f202])).

fof(f182,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) != k5_partfun1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f135,f178])).

fof(f156,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f155,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f155,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f103,f102])).

fof(f102,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f96])).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

% (5280)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f103,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f62,f96,f95,f96,f96])).

fof(f95,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f81,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f83,f93])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (5284)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.49  % (5276)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.49  % (5267)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5267)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (5269)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (5276)Refutation not found, incomplete strategy% (5276)------------------------------
% 0.21/0.51  % (5276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5276)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5276)Memory used [KB]: 1791
% 0.21/0.51  % (5276)Time elapsed: 0.103 s
% 0.21/0.51  % (5276)------------------------------
% 0.21/0.51  % (5276)------------------------------
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f458])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0),
% 0.21/0.51    inference(superposition,[],[f156,f408])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = X1) )),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f326])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ( ! [X1] : (k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.51    inference(superposition,[],[f208,f311])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    ( ! [X0] : (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f305,f204])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    v1_funct_1(k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f54,f202])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    k1_xboole_0 = sK2),
% 0.21/0.51    inference(resolution,[],[f193,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f112,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f87,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    inference(forward_demodulation,[],[f180,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f56,f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    k1_xboole_0 = sK1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    k5_partfun1(sK0,sK1,sK2) != k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f135,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(resolution,[],[f168,f54])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(resolution,[],[f165,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f29])).
% 0.21/0.51  fof(f29,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(resolution,[],[f164,f56])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X4] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~v1_funct_2(sK2,sK0,X4) | ~v1_funct_1(sK2) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = X4) )),
% 0.21/0.51    inference(resolution,[],[f159,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ( ! [X1] : (v1_xboole_0(X1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X1] : (k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,X1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(resolution,[],[f147,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,axiom,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~v1_partfun1(sK2,sK0) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f99,f56])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | k5_partfun1(X0,X1,X2) = k2_enumset1(X2,X2,X2,X2) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f59,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f64,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f82,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | k5_partfun1(X0,X1,X2) != k1_tarski(X2)) & (k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    k2_enumset1(sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f97,f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    sK2 = k3_partfun1(sK2,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f128,f54])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | sK2 = k3_partfun1(sK2,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f61,f56])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2 | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.21/0.51    inference(definition_unfolding,[],[f58,f96])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f291,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(k1_xboole_0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f284,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(k1_xboole_0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f269,f71])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f268,f71])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ( ! [X0] : (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f261,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f124,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f76,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f260,f202])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK2,k1_xboole_0) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f259,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,X0)) | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f258,f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    k1_xboole_0 = sK0),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(superposition,[],[f57,f178])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ( ! [X0] : (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f257,f192])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ( ! [X0] : (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f256,f178])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    ( ! [X0] : (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_partfun1(sK0,sK1,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f255,f202])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f254,f202])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(sK2) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f253,f202])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK2,k1_xboole_0,X0) | ~v1_funct_1(sK2) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f166,f192])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK2,sK0,X0) | ~v1_funct_1(sK2) | k2_enumset1(sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) | k1_xboole_0 = X0 | ~r1_tarski(sK2,k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f164,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f207,f192])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f182,f202])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    k2_enumset1(sK2,sK2,sK2,sK2) != k5_partfun1(sK0,k1_xboole_0,sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f135,f178])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f155,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f103,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f65,f96])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.51  % (5280)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.21/0.51    inference(equality_resolution,[],[f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f62,f96,f95,f96,f96])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f81,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f83,f93])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5267)------------------------------
% 0.21/0.51  % (5267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5267)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5267)Memory used [KB]: 1918
% 0.21/0.51  % (5267)Time elapsed: 0.088 s
% 0.21/0.51  % (5267)------------------------------
% 0.21/0.51  % (5267)------------------------------
% 0.21/0.51  % (5253)Success in time 0.151 s
%------------------------------------------------------------------------------
