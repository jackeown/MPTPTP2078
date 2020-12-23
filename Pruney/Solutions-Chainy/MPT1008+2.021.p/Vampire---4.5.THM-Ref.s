%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:11 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 365 expanded)
%              Number of leaves         :   20 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          :  358 (1395 expanded)
%              Number of equality atoms :  203 ( 660 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f738,plain,(
    $false ),
    inference(subsumption_resolution,[],[f737,f664])).

fof(f664,plain,(
    k1_xboole_0 != k1_tarski(k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f644,f58])).

fof(f58,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f644,plain,(
    k2_relat_1(k1_xboole_0) != k1_tarski(k1_funct_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f147,f634])).

fof(f634,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f633])).

fof(f633,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f130,f613])).

fof(f613,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f612,f147])).

fof(f612,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(equality_resolution,[],[f411])).

fof(f411,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k1_tarski(sK0)
      | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X1))
      | k1_xboole_0 = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f159,f401])).

fof(f401,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f266,f152])).

fof(f152,plain,(
    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f151,f115])).

fof(f115,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f76,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f151,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f143,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f143,plain,(
    v4_relat_1(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X0))
      | k1_tarski(X0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X0))
      | k1_tarski(X0) = X1
      | k1_tarski(X0) = X1
      | k1_tarski(X0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f177,f60])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k1_tarski(X0) = X2
      | k2_tarski(X0,X1) = X2
      | k1_tarski(X1) = X2
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X2
      | ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = X2
      | k1_tarski(X1) = X2
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f175,f60])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = X2
      | k2_tarski(X0,X0) = X2
      | k1_tarski(X1) = X2
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = X2
      | k2_tarski(X0,X1) = X2
      | k2_tarski(X0,X0) = X2
      | k1_tarski(X1) = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2
      | k2_tarski(X0,X1) = X2 ) ),
    inference(superposition,[],[f83,f66])).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f159,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f157,f115])).

fof(f157,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK2)
      | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f130,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f115,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f147,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f55,f145])).

fof(f145,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f737,plain,(
    k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f736,f58])).

fof(f736,plain,(
    k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f705,f340])).

fof(f340,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(equality_resolution,[],[f246])).

fof(f246,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK3(X0) ) ),
    inference(superposition,[],[f127,f65])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_tarski(X2) = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

fof(f127,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f61,f63])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f705,plain,(
    k2_relat_1(sK3(k1_xboole_0)) = k1_tarski(k1_funct_1(sK3(k1_xboole_0),sK0)) ),
    inference(superposition,[],[f248,f667])).

fof(f667,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f647,f300])).

fof(f300,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f154,f299])).

% (2213)Refutation not found, incomplete strategy% (2213)------------------------------
% (2213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2213)Termination reason: Refutation not found, incomplete strategy

% (2213)Memory used [KB]: 10874
% (2213)Time elapsed: 0.172 s
% (2213)------------------------------
% (2213)------------------------------
fof(f299,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f186,f207])).

fof(f207,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k1_xboole_0,X0),X1) ),
    inference(resolution,[],[f156,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f156,plain,(
    ! [X3,X1] : m1_subset_1(k10_relat_1(k1_xboole_0,X3),k1_zfmisc_1(X1)) ),
    inference(backward_demodulation,[],[f150,f154])).

fof(f150,plain,(
    ! [X2,X3,X1] : m1_subset_1(k8_relset_1(X1,X2,k1_xboole_0,X3),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f186,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f73,f59])).

fof(f154,plain,(
    ! [X2,X3,X1] : k8_relset_1(X1,X2,k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f647,plain,(
    k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f165,f634])).

fof(f165,plain,(
    k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1) ),
    inference(subsumption_resolution,[],[f164,f51])).

fof(f164,plain,
    ( k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f162,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f162,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = X0
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f248,plain,(
    ! [X0] : k2_relat_1(sK3(k1_tarski(X0))) = k1_tarski(k1_funct_1(sK3(k1_tarski(X0)),X0)) ),
    inference(equality_resolution,[],[f161])).

fof(f161,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) != X2
      | k2_relat_1(sK3(X2)) = k1_tarski(k1_funct_1(sK3(X2),X1)) ) ),
    inference(forward_demodulation,[],[f160,f65])).

fof(f160,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) != k1_relat_1(sK3(X2))
      | k2_relat_1(sK3(X2)) = k1_tarski(k1_funct_1(sK3(X2),X1)) ) ),
    inference(subsumption_resolution,[],[f158,f63])).

fof(f158,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) != k1_relat_1(sK3(X2))
      | k2_relat_1(sK3(X2)) = k1_tarski(k1_funct_1(sK3(X2),X1))
      | ~ v1_relat_1(sK3(X2)) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (2194)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (2214)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (2214)Refutation not found, incomplete strategy% (2214)------------------------------
% 0.21/0.54  % (2214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2214)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2214)Memory used [KB]: 1663
% 0.21/0.54  % (2214)Time elapsed: 0.111 s
% 0.21/0.54  % (2214)------------------------------
% 0.21/0.54  % (2214)------------------------------
% 0.21/0.55  % (2186)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (2186)Refutation not found, incomplete strategy% (2186)------------------------------
% 0.21/0.55  % (2186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2192)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (2200)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (2186)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (2186)Memory used [KB]: 1663
% 0.21/0.57  % (2186)Time elapsed: 0.080 s
% 0.21/0.57  % (2186)------------------------------
% 0.21/0.57  % (2186)------------------------------
% 0.21/0.58  % (2195)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.58  % (2196)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (2191)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (2190)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.60/0.58  % (2189)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.60/0.59  % (2185)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.60/0.60  % (2209)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.60/0.60  % (2188)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.60/0.60  % (2187)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.60/0.60  % (2213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.60/0.60  % (2212)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.60/0.60  % (2212)Refutation not found, incomplete strategy% (2212)------------------------------
% 1.60/0.60  % (2212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (2212)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (2212)Memory used [KB]: 6268
% 1.60/0.60  % (2212)Time elapsed: 0.170 s
% 1.60/0.60  % (2212)------------------------------
% 1.60/0.60  % (2212)------------------------------
% 1.60/0.60  % (2207)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.87/0.60  % (2195)Refutation not found, incomplete strategy% (2195)------------------------------
% 1.87/0.60  % (2195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (2195)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.60  
% 1.87/0.60  % (2195)Memory used [KB]: 10746
% 1.87/0.60  % (2195)Time elapsed: 0.153 s
% 1.87/0.60  % (2195)------------------------------
% 1.87/0.60  % (2195)------------------------------
% 1.87/0.60  % (2204)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.87/0.60  % (2193)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.87/0.60  % (2205)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.87/0.61  % (2210)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.87/0.61  % (2202)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.87/0.61  % (2206)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.87/0.61  % (2201)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.87/0.61  % (2211)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.87/0.61  % (2201)Refutation not found, incomplete strategy% (2201)------------------------------
% 1.87/0.61  % (2201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (2201)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (2201)Memory used [KB]: 10618
% 1.87/0.61  % (2201)Time elapsed: 0.183 s
% 1.87/0.61  % (2201)------------------------------
% 1.87/0.61  % (2201)------------------------------
% 1.87/0.61  % (2211)Refutation not found, incomplete strategy% (2211)------------------------------
% 1.87/0.61  % (2211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (2211)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (2211)Memory used [KB]: 6268
% 1.87/0.61  % (2211)Time elapsed: 0.184 s
% 1.87/0.61  % (2211)------------------------------
% 1.87/0.61  % (2211)------------------------------
% 1.87/0.61  % (2199)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.87/0.62  % (2208)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.87/0.62  % (2197)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.87/0.62  % (2203)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.87/0.62  % (2198)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.87/0.62  % (2203)Refutation not found, incomplete strategy% (2203)------------------------------
% 1.87/0.62  % (2203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (2203)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (2203)Memory used [KB]: 1791
% 1.87/0.62  % (2203)Time elapsed: 0.192 s
% 1.87/0.62  % (2203)------------------------------
% 1.87/0.62  % (2203)------------------------------
% 1.87/0.62  % (2197)Refutation not found, incomplete strategy% (2197)------------------------------
% 1.87/0.62  % (2197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (2197)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (2197)Memory used [KB]: 10746
% 1.87/0.62  % (2197)Time elapsed: 0.194 s
% 1.87/0.62  % (2197)------------------------------
% 1.87/0.62  % (2197)------------------------------
% 1.87/0.62  % (2192)Refutation found. Thanks to Tanya!
% 1.87/0.62  % SZS status Theorem for theBenchmark
% 1.87/0.62  % SZS output start Proof for theBenchmark
% 1.87/0.62  fof(f738,plain,(
% 1.87/0.62    $false),
% 1.87/0.62    inference(subsumption_resolution,[],[f737,f664])).
% 1.87/0.62  fof(f664,plain,(
% 1.87/0.62    k1_xboole_0 != k1_tarski(k1_funct_1(k1_xboole_0,sK0))),
% 1.87/0.62    inference(forward_demodulation,[],[f644,f58])).
% 1.87/0.62  fof(f58,plain,(
% 1.87/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.87/0.62    inference(cnf_transformation,[],[f11])).
% 1.87/0.62  fof(f11,axiom,(
% 1.87/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.87/0.62  fof(f644,plain,(
% 1.87/0.62    k2_relat_1(k1_xboole_0) != k1_tarski(k1_funct_1(k1_xboole_0,sK0))),
% 1.87/0.62    inference(backward_demodulation,[],[f147,f634])).
% 1.87/0.62  fof(f634,plain,(
% 1.87/0.62    k1_xboole_0 = sK2),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f633])).
% 1.87/0.62  fof(f633,plain,(
% 1.87/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 1.87/0.62    inference(superposition,[],[f130,f613])).
% 1.87/0.62  fof(f613,plain,(
% 1.87/0.62    k1_xboole_0 = k1_relat_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f612,f147])).
% 1.87/0.62  fof(f612,plain,(
% 1.87/0.62    k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.87/0.62    inference(equality_resolution,[],[f411])).
% 1.87/0.62  fof(f411,plain,(
% 1.87/0.62    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK0) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X1)) | k1_xboole_0 = k1_relat_1(sK2)) )),
% 1.87/0.62    inference(superposition,[],[f159,f401])).
% 1.87/0.62  fof(f401,plain,(
% 1.87/0.62    k1_tarski(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.87/0.62    inference(resolution,[],[f266,f152])).
% 1.87/0.62  fof(f152,plain,(
% 1.87/0.62    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))),
% 1.87/0.62    inference(subsumption_resolution,[],[f151,f115])).
% 1.87/0.62  fof(f115,plain,(
% 1.87/0.62    v1_relat_1(sK2)),
% 1.87/0.62    inference(resolution,[],[f76,f53])).
% 1.87/0.62  fof(f53,plain,(
% 1.87/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.87/0.62    inference(cnf_transformation,[],[f42])).
% 1.87/0.62  fof(f42,plain,(
% 1.87/0.62    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f41])).
% 1.87/0.62  fof(f41,plain,(
% 1.87/0.62    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f27,plain,(
% 1.87/0.62    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.87/0.62    inference(flattening,[],[f26])).
% 1.87/0.62  fof(f26,plain,(
% 1.87/0.62    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.87/0.62    inference(ennf_transformation,[],[f22])).
% 1.87/0.62  fof(f22,negated_conjecture,(
% 1.87/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.87/0.62    inference(negated_conjecture,[],[f21])).
% 1.87/0.62  fof(f21,conjecture,(
% 1.87/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.87/0.62  fof(f76,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f33])).
% 1.87/0.62  fof(f33,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f14])).
% 1.87/0.62  fof(f14,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.87/0.62  fof(f151,plain,(
% 1.87/0.62    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 1.87/0.62    inference(resolution,[],[f143,f67])).
% 1.87/0.62  fof(f67,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f45])).
% 1.87/0.62  fof(f45,plain,(
% 1.87/0.62    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(nnf_transformation,[],[f30])).
% 1.87/0.62  fof(f30,plain,(
% 1.87/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(ennf_transformation,[],[f10])).
% 1.87/0.62  fof(f10,axiom,(
% 1.87/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.87/0.62  fof(f143,plain,(
% 1.87/0.62    v4_relat_1(sK2,k1_tarski(sK0))),
% 1.87/0.62    inference(resolution,[],[f78,f53])).
% 1.87/0.62  fof(f78,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f35])).
% 1.87/0.62  fof(f35,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f23])).
% 1.87/0.62  fof(f23,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.87/0.62    inference(pure_predicate_removal,[],[f15])).
% 1.87/0.62  fof(f15,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.87/0.62  fof(f266,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_xboole_0 = X1) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f265])).
% 1.87/0.62  fof(f265,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_tarski(X0) = X1 | k1_tarski(X0) = X1 | k1_xboole_0 = X1) )),
% 1.87/0.62    inference(superposition,[],[f177,f60])).
% 1.87/0.62  fof(f60,plain,(
% 1.87/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f3])).
% 1.87/0.62  fof(f3,axiom,(
% 1.87/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.87/0.62  fof(f177,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_tarski(X0,X1)) | k1_tarski(X0) = X2 | k2_tarski(X0,X1) = X2 | k1_tarski(X1) = X2 | k1_xboole_0 = X2) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f176])).
% 1.87/0.62  fof(f176,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (k1_tarski(X0) = X2 | ~r1_tarski(X2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = X2 | k1_tarski(X1) = X2 | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 1.87/0.62    inference(forward_demodulation,[],[f175,f60])).
% 1.87/0.62  fof(f175,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = X2 | k2_tarski(X0,X0) = X2 | k1_tarski(X1) = X2 | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f174])).
% 1.87/0.62  fof(f174,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = X2 | k2_tarski(X0,X1) = X2 | k2_tarski(X0,X0) = X2 | k1_tarski(X1) = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k1_xboole_0 = X2 | k2_tarski(X0,X1) = X2) )),
% 1.87/0.62    inference(superposition,[],[f83,f66])).
% 1.87/0.62  fof(f66,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f4])).
% 1.87/0.62  fof(f4,axiom,(
% 1.87/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.87/0.62  fof(f83,plain,(
% 1.87/0.62    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | k1_enumset1(X0,X1,X2) = X3) )),
% 1.87/0.62    inference(cnf_transformation,[],[f50])).
% 1.87/0.62  fof(f50,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.87/0.62    inference(flattening,[],[f49])).
% 1.87/0.62  fof(f49,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.87/0.62    inference(nnf_transformation,[],[f40])).
% 1.87/0.62  fof(f40,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.87/0.62    inference(ennf_transformation,[],[f6])).
% 1.87/0.62  fof(f6,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.87/0.62  fof(f159,plain,(
% 1.87/0.62    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0))) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f157,f115])).
% 1.87/0.62  fof(f157,plain,(
% 1.87/0.62    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k1_tarski(k1_funct_1(sK2,X0)) | ~v1_relat_1(sK2)) )),
% 1.87/0.62    inference(resolution,[],[f69,f51])).
% 1.87/0.62  fof(f51,plain,(
% 1.87/0.62    v1_funct_1(sK2)),
% 1.87/0.62    inference(cnf_transformation,[],[f42])).
% 1.87/0.62  fof(f69,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f32])).
% 1.87/0.62  fof(f32,plain,(
% 1.87/0.62    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(flattening,[],[f31])).
% 1.87/0.62  fof(f31,plain,(
% 1.87/0.62    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.87/0.62    inference(ennf_transformation,[],[f13])).
% 1.87/0.62  fof(f13,axiom,(
% 1.87/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.87/0.62  fof(f130,plain,(
% 1.87/0.62    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.87/0.62    inference(resolution,[],[f115,f61])).
% 1.87/0.62  fof(f61,plain,(
% 1.87/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f29])).
% 1.87/0.62  fof(f29,plain,(
% 1.87/0.62    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(flattening,[],[f28])).
% 1.87/0.62  fof(f28,plain,(
% 1.87/0.62    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f12])).
% 1.87/0.62  fof(f12,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.87/0.62  fof(f147,plain,(
% 1.87/0.62    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.87/0.62    inference(backward_demodulation,[],[f55,f145])).
% 1.87/0.62  fof(f145,plain,(
% 1.87/0.62    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.87/0.62    inference(resolution,[],[f77,f53])).
% 1.87/0.62  fof(f77,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f34])).
% 1.87/0.62  fof(f34,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f17])).
% 1.87/0.62  fof(f17,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.87/0.62  fof(f55,plain,(
% 1.87/0.62    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.87/0.62    inference(cnf_transformation,[],[f42])).
% 1.87/0.62  fof(f737,plain,(
% 1.87/0.62    k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,sK0))),
% 1.87/0.62    inference(forward_demodulation,[],[f736,f58])).
% 1.87/0.62  fof(f736,plain,(
% 1.87/0.62    k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,sK0))),
% 1.87/0.62    inference(forward_demodulation,[],[f705,f340])).
% 1.87/0.62  fof(f340,plain,(
% 1.87/0.62    k1_xboole_0 = sK3(k1_xboole_0)),
% 1.87/0.62    inference(equality_resolution,[],[f246])).
% 1.87/0.62  fof(f246,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK3(X0)) )),
% 1.87/0.62    inference(superposition,[],[f127,f65])).
% 1.87/0.62  fof(f65,plain,(
% 1.87/0.62    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f44])).
% 1.87/0.62  fof(f44,plain,(
% 1.87/0.62    ! [X0] : (k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 1.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f43])).
% 1.87/0.62  fof(f43,plain,(
% 1.87/0.62    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f24,plain,(
% 1.87/0.62    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.87/0.62    inference(pure_predicate_removal,[],[f19])).
% 1.87/0.62  fof(f19,axiom,(
% 1.87/0.62    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_tarski(X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).
% 1.87/0.62  fof(f127,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = sK3(X0)) )),
% 1.87/0.62    inference(resolution,[],[f61,f63])).
% 1.87/0.62  fof(f63,plain,(
% 1.87/0.62    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f44])).
% 1.87/0.62  fof(f705,plain,(
% 1.87/0.62    k2_relat_1(sK3(k1_xboole_0)) = k1_tarski(k1_funct_1(sK3(k1_xboole_0),sK0))),
% 1.87/0.62    inference(superposition,[],[f248,f667])).
% 1.87/0.62  fof(f667,plain,(
% 1.87/0.62    k1_xboole_0 = k1_tarski(sK0)),
% 1.87/0.62    inference(forward_demodulation,[],[f647,f300])).
% 1.87/0.62  fof(f300,plain,(
% 1.87/0.62    ( ! [X2,X3,X1] : (k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X3)) )),
% 1.87/0.62    inference(backward_demodulation,[],[f154,f299])).
% 1.87/0.62  % (2213)Refutation not found, incomplete strategy% (2213)------------------------------
% 1.87/0.62  % (2213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (2213)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (2213)Memory used [KB]: 10874
% 1.87/0.62  % (2213)Time elapsed: 0.172 s
% 1.87/0.62  % (2213)------------------------------
% 1.87/0.62  % (2213)------------------------------
% 1.87/0.62  fof(f299,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.87/0.62    inference(resolution,[],[f186,f207])).
% 1.87/0.62  fof(f207,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),X1)) )),
% 1.87/0.62    inference(resolution,[],[f156,f73])).
% 1.87/0.62  fof(f73,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f48])).
% 1.87/0.62  fof(f48,plain,(
% 1.87/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.87/0.62    inference(nnf_transformation,[],[f8])).
% 1.87/0.62  fof(f8,axiom,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.87/0.62  fof(f156,plain,(
% 1.87/0.62    ( ! [X3,X1] : (m1_subset_1(k10_relat_1(k1_xboole_0,X3),k1_zfmisc_1(X1))) )),
% 1.87/0.62    inference(backward_demodulation,[],[f150,f154])).
% 1.87/0.62  fof(f150,plain,(
% 1.87/0.62    ( ! [X2,X3,X1] : (m1_subset_1(k8_relset_1(X1,X2,k1_xboole_0,X3),k1_zfmisc_1(X1))) )),
% 1.87/0.62    inference(resolution,[],[f81,f59])).
% 1.87/0.62  fof(f59,plain,(
% 1.87/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f7])).
% 1.87/0.62  fof(f7,axiom,(
% 1.87/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.87/0.62  fof(f81,plain,(
% 1.87/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f38])).
% 1.87/0.62  fof(f38,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f16])).
% 1.87/0.62  fof(f16,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.87/0.62  fof(f186,plain,(
% 1.87/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.87/0.62    inference(resolution,[],[f104,f72])).
% 1.87/0.62  fof(f72,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f47])).
% 1.87/0.62  fof(f47,plain,(
% 1.87/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.87/0.62    inference(flattening,[],[f46])).
% 1.87/0.62  fof(f46,plain,(
% 1.87/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.87/0.62    inference(nnf_transformation,[],[f2])).
% 1.87/0.62  fof(f2,axiom,(
% 1.87/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.87/0.62  fof(f104,plain,(
% 1.87/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.62    inference(resolution,[],[f73,f59])).
% 1.87/0.62  fof(f154,plain,(
% 1.87/0.62    ( ! [X2,X3,X1] : (k8_relset_1(X1,X2,k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,X3)) )),
% 1.87/0.62    inference(resolution,[],[f82,f59])).
% 1.87/0.62  fof(f82,plain,(
% 1.87/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f39])).
% 1.87/0.62  fof(f39,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f18])).
% 1.87/0.62  fof(f18,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.87/0.62  fof(f647,plain,(
% 1.87/0.62    k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,k1_xboole_0,sK1)),
% 1.87/0.62    inference(backward_demodulation,[],[f165,f634])).
% 1.87/0.62  fof(f165,plain,(
% 1.87/0.62    k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1)),
% 1.87/0.62    inference(subsumption_resolution,[],[f164,f51])).
% 1.87/0.62  fof(f164,plain,(
% 1.87/0.62    k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f163,f53])).
% 1.87/0.62  fof(f163,plain,(
% 1.87/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(subsumption_resolution,[],[f162,f54])).
% 1.87/0.62  fof(f54,plain,(
% 1.87/0.62    k1_xboole_0 != sK1),
% 1.87/0.62    inference(cnf_transformation,[],[f42])).
% 1.87/0.62  fof(f162,plain,(
% 1.87/0.62    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | k1_tarski(sK0) = k8_relset_1(k1_tarski(sK0),sK1,sK2,sK1) | ~v1_funct_1(sK2)),
% 1.87/0.62    inference(resolution,[],[f79,f52])).
% 1.87/0.62  fof(f52,plain,(
% 1.87/0.62    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.87/0.62    inference(cnf_transformation,[],[f42])).
% 1.87/0.62  fof(f79,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_1(X2)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f37])).
% 1.87/0.62  fof(f37,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.87/0.62    inference(flattening,[],[f36])).
% 1.87/0.62  fof(f36,plain,(
% 1.87/0.62    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.87/0.62    inference(ennf_transformation,[],[f20])).
% 1.87/0.62  fof(f20,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 1.87/0.62  fof(f248,plain,(
% 1.87/0.62    ( ! [X0] : (k2_relat_1(sK3(k1_tarski(X0))) = k1_tarski(k1_funct_1(sK3(k1_tarski(X0)),X0))) )),
% 1.87/0.62    inference(equality_resolution,[],[f161])).
% 1.87/0.62  fof(f161,plain,(
% 1.87/0.62    ( ! [X2,X1] : (k1_tarski(X1) != X2 | k2_relat_1(sK3(X2)) = k1_tarski(k1_funct_1(sK3(X2),X1))) )),
% 1.87/0.62    inference(forward_demodulation,[],[f160,f65])).
% 1.87/0.62  fof(f160,plain,(
% 1.87/0.62    ( ! [X2,X1] : (k1_tarski(X1) != k1_relat_1(sK3(X2)) | k2_relat_1(sK3(X2)) = k1_tarski(k1_funct_1(sK3(X2),X1))) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f158,f63])).
% 1.87/0.62  fof(f158,plain,(
% 1.87/0.62    ( ! [X2,X1] : (k1_tarski(X1) != k1_relat_1(sK3(X2)) | k2_relat_1(sK3(X2)) = k1_tarski(k1_funct_1(sK3(X2),X1)) | ~v1_relat_1(sK3(X2))) )),
% 1.87/0.62    inference(resolution,[],[f69,f64])).
% 1.87/0.63  fof(f64,plain,(
% 1.87/0.63    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.87/0.63    inference(cnf_transformation,[],[f44])).
% 1.87/0.63  % SZS output end Proof for theBenchmark
% 1.87/0.63  % (2192)------------------------------
% 1.87/0.63  % (2192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (2192)Termination reason: Refutation
% 1.87/0.63  
% 1.87/0.63  % (2192)Memory used [KB]: 2302
% 1.87/0.63  % (2192)Time elapsed: 0.153 s
% 1.87/0.63  % (2192)------------------------------
% 1.87/0.63  % (2192)------------------------------
% 1.87/0.63  % (2184)Success in time 0.254 s
%------------------------------------------------------------------------------
