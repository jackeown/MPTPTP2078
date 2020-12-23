%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:17 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  168 (16083 expanded)
%              Number of leaves         :   18 (3884 expanded)
%              Depth                    :   45
%              Number of atoms          :  482 (93860 expanded)
%              Number of equality atoms :  140 (14801 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f658,plain,(
    $false ),
    inference(subsumption_resolution,[],[f657,f166])).

fof(f166,plain,(
    ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    inference(superposition,[],[f87,f153])).

fof(f153,plain,(
    ! [X5] : k1_xboole_0 = sK5(k1_xboole_0,X5) ),
    inference(subsumption_resolution,[],[f148,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f148,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0,X5))
      | k1_xboole_0 = sK5(k1_xboole_0,X5) ) ),
    inference(resolution,[],[f75,f120])).

fof(f120,plain,(
    ! [X0] : r1_tarski(sK5(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f118,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f118,plain,(
    ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f84,f102])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK5(X0,X1),X0,X1)
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1))
      & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK5(X0,X1),X0,X1)
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f87,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f51])).

fof(f657,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f656,f647])).

fof(f647,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f646,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f646,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f645,f384])).

fof(f384,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f381,f255])).

fof(f255,plain,(
    ! [X4,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0) ),
    inference(resolution,[],[f237,f63])).

fof(f237,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
      | k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    inference(resolution,[],[f89,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f381,plain,(
    ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f378,f192])).

fof(f192,plain,(
    ! [X2,X3] : sP0(X2,k1_xboole_0,X3) ),
    inference(resolution,[],[f179,f63])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X0,X2))
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f95,f80])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f378,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f104,f166])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f645,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f644,f604])).

fof(f604,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f603,f101])).

fof(f603,plain,(
    sK3 = k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f602,f556])).

fof(f556,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f555,f123])).

fof(f123,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f555,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f554,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f554,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f553,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f553,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f551,f490])).

fof(f490,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f368,f475])).

fof(f475,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f473,f238])).

fof(f238,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f89,f57])).

fof(f473,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f470,f180])).

fof(f180,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f95,f57])).

fof(f470,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f368,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f367,f123])).

fof(f367,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f366,f55])).

fof(f366,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f365,f70])).

fof(f365,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(subsumption_resolution,[],[f268,f360])).

fof(f360,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f356,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f88,f80])).

fof(f356,plain,(
    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f355,f123])).

fof(f355,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f354,f55])).

fof(f354,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f353,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f353,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f352,f123])).

fof(f352,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f351,f55])).

fof(f351,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f266,f70])).

fof(f266,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) ),
    inference(backward_demodulation,[],[f227,f265])).

fof(f265,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f261,f59])).

fof(f59,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f261,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f90,f57])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f227,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f217,f223])).

fof(f223,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f222,f123])).

fof(f222,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f221,f55])).

fof(f221,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f217,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f202,f216])).

fof(f216,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f215,f123])).

fof(f215,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f214,f55])).

fof(f214,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f71,f58])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f202,plain,(
    ! [X2] :
      ( r1_tarski(X2,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f68,f79])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f268,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f225,f265])).

fof(f225,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f219,f223])).

fof(f219,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f68,f216])).

fof(f551,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f550,f60])).

fof(f60,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f550,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f549,f123])).

fof(f549,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f548,f55])).

fof(f548,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f489,f70])).

fof(f489,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f364,f475])).

fof(f364,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f269,f360])).

fof(f269,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f224,f265])).

fof(f224,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f220,f223])).

fof(f220,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f67,f216])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f602,plain,(
    sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f601,f63])).

fof(f601,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f562,f101])).

fof(f562,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f145,f556])).

fof(f145,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f75,f112])).

fof(f112,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f79,f57])).

fof(f644,plain,(
    k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f643,f63])).

fof(f643,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f642,f102])).

fof(f642,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f576,f604])).

fof(f576,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f361,f556])).

fof(f361,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f356,f75])).

fof(f656,plain,(
    ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f655,f151])).

fof(f151,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f117,f149])).

fof(f149,plain,(
    ! [X4] : k1_xboole_0 = sK5(X4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f147,f63])).

fof(f147,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_xboole_0,sK5(X4,k1_xboole_0))
      | k1_xboole_0 = sK5(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f75,f119])).

fof(f119,plain,(
    ! [X0] : r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f117,f79])).

% (24354)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f117,plain,(
    ! [X0] : m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f84,f101])).

fof(f655,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f654,f647])).

fof(f654,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f650,f110])).

fof(f110,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f65,f62])).

fof(f62,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f65,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f650,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f617,f647])).

fof(f617,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f616,f604])).

fof(f616,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f613,f604])).

fof(f613,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f599,f604])).

fof(f599,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f598,f556])).

fof(f598,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f560,f102])).

fof(f560,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f60,f556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (24365)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.48  % (24357)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.48  % (24349)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (24347)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24360)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (24346)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (24370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (24343)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.51  % (24349)Refutation found. Thanks to Tanya!
% 1.22/0.51  % SZS status Theorem for theBenchmark
% 1.22/0.51  % SZS output start Proof for theBenchmark
% 1.22/0.51  fof(f658,plain,(
% 1.22/0.51    $false),
% 1.22/0.51    inference(subsumption_resolution,[],[f657,f166])).
% 1.22/0.51  fof(f166,plain,(
% 1.22/0.51    ( ! [X2] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 1.22/0.51    inference(superposition,[],[f87,f153])).
% 1.22/0.51  fof(f153,plain,(
% 1.22/0.51    ( ! [X5] : (k1_xboole_0 = sK5(k1_xboole_0,X5)) )),
% 1.22/0.51    inference(subsumption_resolution,[],[f148,f63])).
% 1.22/0.51  fof(f63,plain,(
% 1.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f4])).
% 1.22/0.51  fof(f4,axiom,(
% 1.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.22/0.51  fof(f148,plain,(
% 1.22/0.51    ( ! [X5] : (~r1_tarski(k1_xboole_0,sK5(k1_xboole_0,X5)) | k1_xboole_0 = sK5(k1_xboole_0,X5)) )),
% 1.22/0.51    inference(resolution,[],[f75,f120])).
% 1.22/0.51  fof(f120,plain,(
% 1.22/0.51    ( ! [X0] : (r1_tarski(sK5(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.22/0.51    inference(resolution,[],[f118,f79])).
% 1.22/0.51  fof(f79,plain,(
% 1.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f47])).
% 1.22/0.51  fof(f47,plain,(
% 1.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.22/0.51    inference(nnf_transformation,[],[f6])).
% 1.22/0.51  fof(f6,axiom,(
% 1.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.22/0.51  fof(f118,plain,(
% 1.22/0.51    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.22/0.51    inference(superposition,[],[f84,f102])).
% 1.22/0.51  fof(f102,plain,(
% 1.22/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.22/0.51    inference(equality_resolution,[],[f82])).
% 1.22/0.51  fof(f82,plain,(
% 1.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.22/0.51    inference(cnf_transformation,[],[f49])).
% 1.22/0.51  fof(f49,plain,(
% 1.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.22/0.51    inference(flattening,[],[f48])).
% 1.22/0.51  fof(f48,plain,(
% 1.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.22/0.51    inference(nnf_transformation,[],[f5])).
% 1.22/0.51  fof(f5,axiom,(
% 1.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.22/0.51  fof(f84,plain,(
% 1.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.51    inference(cnf_transformation,[],[f51])).
% 1.22/0.51  fof(f51,plain,(
% 1.22/0.51    ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f50])).
% 1.22/0.51  fof(f50,plain,(
% 1.22/0.51    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.22/0.51    introduced(choice_axiom,[])).
% 1.22/0.51  fof(f21,plain,(
% 1.22/0.51    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(pure_predicate_removal,[],[f20])).
% 1.22/0.51  fof(f20,plain,(
% 1.22/0.51    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(pure_predicate_removal,[],[f16])).
% 1.22/0.51  fof(f16,axiom,(
% 1.22/0.51    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.22/0.51  fof(f75,plain,(
% 1.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.22/0.51    inference(cnf_transformation,[],[f42])).
% 1.22/0.51  fof(f42,plain,(
% 1.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.51    inference(flattening,[],[f41])).
% 1.22/0.51  fof(f41,plain,(
% 1.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.51    inference(nnf_transformation,[],[f3])).
% 1.22/0.51  fof(f3,axiom,(
% 1.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.22/0.51  fof(f87,plain,(
% 1.22/0.51    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f51])).
% 1.22/0.51  fof(f657,plain,(
% 1.22/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 1.22/0.51    inference(forward_demodulation,[],[f656,f647])).
% 1.22/0.51  fof(f647,plain,(
% 1.22/0.51    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.22/0.51    inference(forward_demodulation,[],[f646,f101])).
% 1.22/0.51  fof(f101,plain,(
% 1.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.22/0.51    inference(equality_resolution,[],[f83])).
% 1.22/0.51  fof(f83,plain,(
% 1.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.22/0.51    inference(cnf_transformation,[],[f49])).
% 1.22/0.51  fof(f646,plain,(
% 1.22/0.51    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_xboole_0)),
% 1.22/0.51    inference(forward_demodulation,[],[f645,f384])).
% 1.22/0.51  fof(f384,plain,(
% 1.22/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.51    inference(superposition,[],[f381,f255])).
% 1.22/0.51  fof(f255,plain,(
% 1.22/0.51    ( ! [X4,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0)) )),
% 1.22/0.51    inference(resolution,[],[f237,f63])).
% 1.22/0.51  fof(f237,plain,(
% 1.22/0.51    ( ! [X2,X3,X1] : (~r1_tarski(X3,k2_zfmisc_1(X1,X2)) | k1_relset_1(X1,X2,X3) = k1_relat_1(X3)) )),
% 1.22/0.51    inference(resolution,[],[f89,f80])).
% 1.22/0.51  fof(f80,plain,(
% 1.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f47])).
% 1.22/0.51  fof(f89,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f32])).
% 1.22/0.51  fof(f32,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(ennf_transformation,[],[f13])).
% 1.22/0.51  fof(f13,axiom,(
% 1.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.22/0.51  fof(f381,plain,(
% 1.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.22/0.51    inference(subsumption_resolution,[],[f378,f192])).
% 1.22/0.51  fof(f192,plain,(
% 1.22/0.51    ( ! [X2,X3] : (sP0(X2,k1_xboole_0,X3)) )),
% 1.22/0.51    inference(resolution,[],[f179,f63])).
% 1.22/0.51  fof(f179,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(X0,X2)) | sP0(X0,X1,X2)) )),
% 1.22/0.51    inference(resolution,[],[f95,f80])).
% 1.22/0.51  fof(f95,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f54])).
% 1.22/0.51  fof(f54,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(nnf_transformation,[],[f38])).
% 1.22/0.51  fof(f38,plain,(
% 1.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(definition_folding,[],[f35,f37])).
% 1.22/0.51  fof(f37,plain,(
% 1.22/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.22/0.51  fof(f35,plain,(
% 1.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(flattening,[],[f34])).
% 1.22/0.51  fof(f34,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(ennf_transformation,[],[f15])).
% 1.22/0.51  fof(f15,axiom,(
% 1.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.22/0.51  fof(f378,plain,(
% 1.22/0.51    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.22/0.51    inference(resolution,[],[f104,f166])).
% 1.22/0.51  fof(f104,plain,(
% 1.22/0.51    ( ! [X2,X1] : (~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) | ~sP0(k1_xboole_0,X1,X2)) )),
% 1.22/0.51    inference(equality_resolution,[],[f92])).
% 1.22/0.51  fof(f92,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f53])).
% 1.22/0.51  fof(f53,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.22/0.51    inference(rectify,[],[f52])).
% 1.22/0.51  fof(f52,plain,(
% 1.22/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.22/0.51    inference(nnf_transformation,[],[f37])).
% 1.22/0.51  fof(f645,plain,(
% 1.22/0.51    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0))),
% 1.22/0.51    inference(forward_demodulation,[],[f644,f604])).
% 1.22/0.51  fof(f604,plain,(
% 1.22/0.51    k1_xboole_0 = sK3),
% 1.22/0.51    inference(forward_demodulation,[],[f603,f101])).
% 1.22/0.51  fof(f603,plain,(
% 1.22/0.51    sK3 = k2_zfmisc_1(sK1,k1_xboole_0)),
% 1.22/0.51    inference(forward_demodulation,[],[f602,f556])).
% 1.22/0.51  fof(f556,plain,(
% 1.22/0.51    k1_xboole_0 = sK2),
% 1.22/0.51    inference(subsumption_resolution,[],[f555,f123])).
% 1.22/0.51  fof(f123,plain,(
% 1.22/0.51    v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f88,f57])).
% 1.22/0.51  fof(f57,plain,(
% 1.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.22/0.51    inference(cnf_transformation,[],[f40])).
% 1.22/0.51  fof(f40,plain,(
% 1.22/0.51    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f39])).
% 1.22/0.51  fof(f39,plain,(
% 1.22/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.22/0.51    introduced(choice_axiom,[])).
% 1.22/0.51  fof(f23,plain,(
% 1.22/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.22/0.51    inference(flattening,[],[f22])).
% 1.22/0.51  fof(f22,plain,(
% 1.22/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.22/0.51    inference(ennf_transformation,[],[f19])).
% 1.22/0.51  fof(f19,negated_conjecture,(
% 1.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.22/0.51    inference(negated_conjecture,[],[f18])).
% 1.22/0.51  fof(f18,conjecture,(
% 1.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.22/0.51  fof(f88,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f31])).
% 1.22/0.51  fof(f31,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(ennf_transformation,[],[f12])).
% 1.22/0.51  fof(f12,axiom,(
% 1.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.22/0.51  fof(f555,plain,(
% 1.22/0.51    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f554,f55])).
% 1.22/0.51  fof(f55,plain,(
% 1.22/0.51    v1_funct_1(sK3)),
% 1.22/0.51    inference(cnf_transformation,[],[f40])).
% 1.22/0.51  fof(f554,plain,(
% 1.22/0.51    k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f553,f70])).
% 1.22/0.51  fof(f70,plain,(
% 1.22/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f27])).
% 1.22/0.51  fof(f27,plain,(
% 1.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.51    inference(flattening,[],[f26])).
% 1.22/0.51  fof(f26,plain,(
% 1.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f9])).
% 1.22/0.51  fof(f9,axiom,(
% 1.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.22/0.51  fof(f553,plain,(
% 1.22/0.51    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 1.22/0.51    inference(subsumption_resolution,[],[f551,f490])).
% 1.22/0.51  fof(f490,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k1_xboole_0 = sK2),
% 1.22/0.51    inference(superposition,[],[f368,f475])).
% 1.22/0.51  fof(f475,plain,(
% 1.22/0.51    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.22/0.51    inference(superposition,[],[f473,f238])).
% 1.22/0.51  fof(f238,plain,(
% 1.22/0.51    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.22/0.51    inference(resolution,[],[f89,f57])).
% 1.22/0.51  fof(f473,plain,(
% 1.22/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.22/0.51    inference(subsumption_resolution,[],[f470,f180])).
% 1.22/0.51  fof(f180,plain,(
% 1.22/0.51    sP0(sK1,sK3,sK2)),
% 1.22/0.51    inference(resolution,[],[f95,f57])).
% 1.22/0.51  fof(f470,plain,(
% 1.22/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~sP0(sK1,sK3,sK2)),
% 1.22/0.51    inference(resolution,[],[f91,f56])).
% 1.22/0.51  fof(f56,plain,(
% 1.22/0.51    v1_funct_2(sK3,sK1,sK2)),
% 1.22/0.51    inference(cnf_transformation,[],[f40])).
% 1.22/0.51  fof(f91,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f53])).
% 1.22/0.51  fof(f368,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 1.22/0.51    inference(subsumption_resolution,[],[f367,f123])).
% 1.22/0.51  fof(f367,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f366,f55])).
% 1.22/0.51  fof(f366,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f365,f70])).
% 1.22/0.51  fof(f365,plain,(
% 1.22/0.51    ~v1_funct_1(k2_funct_1(sK3)) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 1.22/0.51    inference(subsumption_resolution,[],[f268,f360])).
% 1.22/0.51  fof(f360,plain,(
% 1.22/0.51    v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(resolution,[],[f356,f124])).
% 1.22/0.51  fof(f124,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 1.22/0.51    inference(resolution,[],[f88,f80])).
% 1.22/0.51  fof(f356,plain,(
% 1.22/0.51    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))),
% 1.22/0.51    inference(subsumption_resolution,[],[f355,f123])).
% 1.22/0.51  fof(f355,plain,(
% 1.22/0.51    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f354,f55])).
% 1.22/0.51  fof(f354,plain,(
% 1.22/0.51    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f353,f69])).
% 1.22/0.51  fof(f69,plain,(
% 1.22/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f27])).
% 1.22/0.51  fof(f353,plain,(
% 1.22/0.51    ~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))),
% 1.22/0.51    inference(subsumption_resolution,[],[f352,f123])).
% 1.22/0.51  fof(f352,plain,(
% 1.22/0.51    ~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f351,f55])).
% 1.22/0.51  fof(f351,plain,(
% 1.22/0.51    ~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f266,f70])).
% 1.22/0.51  fof(f266,plain,(
% 1.22/0.51    ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))),
% 1.22/0.51    inference(backward_demodulation,[],[f227,f265])).
% 1.22/0.51  fof(f265,plain,(
% 1.22/0.51    sK2 = k2_relat_1(sK3)),
% 1.22/0.51    inference(forward_demodulation,[],[f261,f59])).
% 1.22/0.51  fof(f59,plain,(
% 1.22/0.51    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.22/0.51    inference(cnf_transformation,[],[f40])).
% 1.22/0.51  fof(f261,plain,(
% 1.22/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f90,f57])).
% 1.22/0.51  fof(f90,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f33])).
% 1.22/0.51  fof(f33,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.51    inference(ennf_transformation,[],[f14])).
% 1.22/0.51  fof(f14,axiom,(
% 1.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.22/0.51  fof(f227,plain,(
% 1.22/0.51    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f217,f223])).
% 1.22/0.51  fof(f223,plain,(
% 1.22/0.51    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(subsumption_resolution,[],[f222,f123])).
% 1.22/0.51  fof(f222,plain,(
% 1.22/0.51    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f221,f55])).
% 1.22/0.51  fof(f221,plain,(
% 1.22/0.51    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f72,f58])).
% 1.22/0.51  fof(f58,plain,(
% 1.22/0.51    v2_funct_1(sK3)),
% 1.22/0.51    inference(cnf_transformation,[],[f40])).
% 1.22/0.51  fof(f72,plain,(
% 1.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f29])).
% 1.22/0.51  fof(f29,plain,(
% 1.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.51    inference(flattening,[],[f28])).
% 1.22/0.51  fof(f28,plain,(
% 1.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f11])).
% 1.22/0.51  fof(f11,axiom,(
% 1.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.22/0.51  fof(f217,plain,(
% 1.22/0.51    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(superposition,[],[f202,f216])).
% 1.22/0.51  fof(f216,plain,(
% 1.22/0.51    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(subsumption_resolution,[],[f215,f123])).
% 1.22/0.51  fof(f215,plain,(
% 1.22/0.51    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f214,f55])).
% 1.22/0.51  fof(f214,plain,(
% 1.22/0.51    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f71,f58])).
% 1.22/0.51  fof(f71,plain,(
% 1.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f29])).
% 1.22/0.51  fof(f202,plain,(
% 1.22/0.51    ( ! [X2] : (r1_tarski(X2,k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2))) | ~v1_relat_1(X2) | ~v1_funct_1(X2)) )),
% 1.22/0.51    inference(resolution,[],[f68,f79])).
% 1.22/0.51  fof(f68,plain,(
% 1.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f25])).
% 1.22/0.51  fof(f25,plain,(
% 1.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.51    inference(flattening,[],[f24])).
% 1.22/0.51  fof(f24,plain,(
% 1.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f17])).
% 1.22/0.51  fof(f17,axiom,(
% 1.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.22/0.51  fof(f268,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f225,f265])).
% 1.22/0.51  fof(f225,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f219,f223])).
% 1.22/0.51  fof(f219,plain,(
% 1.22/0.51    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(superposition,[],[f68,f216])).
% 1.22/0.51  fof(f551,plain,(
% 1.22/0.51    k1_xboole_0 = sK2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(resolution,[],[f550,f60])).
% 1.22/0.51  fof(f60,plain,(
% 1.22/0.51    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(cnf_transformation,[],[f40])).
% 1.22/0.51  fof(f550,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2),
% 1.22/0.51    inference(subsumption_resolution,[],[f549,f123])).
% 1.22/0.51  fof(f549,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(subsumption_resolution,[],[f548,f55])).
% 1.22/0.51  fof(f548,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.22/0.51    inference(resolution,[],[f489,f70])).
% 1.22/0.51  fof(f489,plain,(
% 1.22/0.51    ~v1_funct_1(k2_funct_1(sK3)) | v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2),
% 1.22/0.51    inference(superposition,[],[f364,f475])).
% 1.22/0.51  fof(f364,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(subsumption_resolution,[],[f269,f360])).
% 1.22/0.51  fof(f269,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f224,f265])).
% 1.22/0.51  fof(f224,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f220,f223])).
% 1.22/0.51  fof(f220,plain,(
% 1.22/0.51    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(superposition,[],[f67,f216])).
% 1.22/0.51  fof(f67,plain,(
% 1.22/0.51    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f25])).
% 1.22/0.51  fof(f602,plain,(
% 1.22/0.51    sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.22/0.51    inference(subsumption_resolution,[],[f601,f63])).
% 1.22/0.51  fof(f601,plain,(
% 1.22/0.51    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.22/0.51    inference(forward_demodulation,[],[f562,f101])).
% 1.22/0.51  fof(f562,plain,(
% 1.22/0.51    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.22/0.51    inference(backward_demodulation,[],[f145,f556])).
% 1.22/0.51  fof(f145,plain,(
% 1.22/0.51    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 1.22/0.51    inference(resolution,[],[f75,f112])).
% 1.22/0.51  fof(f112,plain,(
% 1.22/0.51    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 1.22/0.51    inference(resolution,[],[f79,f57])).
% 1.22/0.51  fof(f644,plain,(
% 1.22/0.51    k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.22/0.51    inference(subsumption_resolution,[],[f643,f63])).
% 1.22/0.51  fof(f643,plain,(
% 1.22/0.51    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.22/0.51    inference(forward_demodulation,[],[f642,f102])).
% 1.22/0.51  fof(f642,plain,(
% 1.22/0.51    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.22/0.51    inference(forward_demodulation,[],[f576,f604])).
% 1.22/0.51  fof(f576,plain,(
% 1.22/0.51    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f361,f556])).
% 1.22/0.51  fof(f361,plain,(
% 1.22/0.51    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 1.22/0.51    inference(resolution,[],[f356,f75])).
% 1.22/0.51  fof(f656,plain,(
% 1.22/0.51    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 1.22/0.51    inference(subsumption_resolution,[],[f655,f151])).
% 1.22/0.51  fof(f151,plain,(
% 1.22/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.22/0.51    inference(backward_demodulation,[],[f117,f149])).
% 1.22/0.51  fof(f149,plain,(
% 1.22/0.51    ( ! [X4] : (k1_xboole_0 = sK5(X4,k1_xboole_0)) )),
% 1.22/0.51    inference(subsumption_resolution,[],[f147,f63])).
% 1.22/0.51  fof(f147,plain,(
% 1.22/0.51    ( ! [X4] : (~r1_tarski(k1_xboole_0,sK5(X4,k1_xboole_0)) | k1_xboole_0 = sK5(X4,k1_xboole_0)) )),
% 1.22/0.51    inference(resolution,[],[f75,f119])).
% 1.22/0.51  fof(f119,plain,(
% 1.22/0.51    ( ! [X0] : (r1_tarski(sK5(X0,k1_xboole_0),k1_xboole_0)) )),
% 1.22/0.51    inference(resolution,[],[f117,f79])).
% 1.22/0.51  % (24354)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.51  fof(f117,plain,(
% 1.22/0.51    ( ! [X0] : (m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 1.22/0.51    inference(superposition,[],[f84,f101])).
% 1.22/0.51  fof(f655,plain,(
% 1.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 1.22/0.51    inference(forward_demodulation,[],[f654,f647])).
% 1.22/0.51  fof(f654,plain,(
% 1.22/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 1.22/0.51    inference(subsumption_resolution,[],[f650,f110])).
% 1.22/0.51  fof(f110,plain,(
% 1.22/0.51    v1_funct_1(k1_xboole_0)),
% 1.22/0.51    inference(superposition,[],[f65,f62])).
% 1.22/0.51  fof(f62,plain,(
% 1.22/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.22/0.51    inference(cnf_transformation,[],[f8])).
% 1.22/0.51  fof(f8,axiom,(
% 1.22/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.22/0.51  fof(f65,plain,(
% 1.22/0.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.22/0.51    inference(cnf_transformation,[],[f10])).
% 1.22/0.51  fof(f10,axiom,(
% 1.22/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.22/0.51  fof(f650,plain,(
% 1.22/0.51    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 1.22/0.51    inference(backward_demodulation,[],[f617,f647])).
% 1.22/0.51  fof(f617,plain,(
% 1.22/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 1.22/0.51    inference(forward_demodulation,[],[f616,f604])).
% 1.22/0.51  fof(f616,plain,(
% 1.22/0.51    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 1.22/0.51    inference(forward_demodulation,[],[f613,f604])).
% 1.22/0.51  fof(f613,plain,(
% 1.22/0.51    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 1.22/0.51    inference(backward_demodulation,[],[f599,f604])).
% 1.22/0.51  fof(f599,plain,(
% 1.22/0.51    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(forward_demodulation,[],[f598,f556])).
% 1.22/0.51  fof(f598,plain,(
% 1.22/0.51    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(forward_demodulation,[],[f560,f102])).
% 1.22/0.51  fof(f560,plain,(
% 1.22/0.51    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.22/0.51    inference(backward_demodulation,[],[f60,f556])).
% 1.22/0.51  % SZS output end Proof for theBenchmark
% 1.22/0.51  % (24349)------------------------------
% 1.22/0.51  % (24349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (24349)Termination reason: Refutation
% 1.22/0.51  
% 1.22/0.51  % (24349)Memory used [KB]: 6652
% 1.22/0.51  % (24349)Time elapsed: 0.117 s
% 1.22/0.51  % (24349)------------------------------
% 1.22/0.51  % (24349)------------------------------
% 1.22/0.51  % (24346)Refutation not found, incomplete strategy% (24346)------------------------------
% 1.22/0.51  % (24346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (24341)Success in time 0.16 s
%------------------------------------------------------------------------------
