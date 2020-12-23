%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  161 (12389 expanded)
%              Number of leaves         :   17 (2988 expanded)
%              Depth                    :   42
%              Number of atoms          :  455 (72362 expanded)
%              Number of equality atoms :  137 (12266 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f883,plain,(
    $false ),
    inference(subsumption_resolution,[],[f882,f536])).

fof(f536,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f535,f228])).

fof(f228,plain,(
    ! [X0,X1] : sP0(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f535,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f534])).

fof(f534,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f89,f442])).

fof(f442,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f437,f132])).

fof(f132,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f130,f117])).

fof(f117,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f68,f96])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f130,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f129,f99])).

fof(f99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f74,f55])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f129,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f122,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f122,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f77,f55])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f437,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f76,f55])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f882,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f881,f870])).

fof(f870,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f869,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f869,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f868,f132])).

fof(f868,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f867,f821])).

fof(f821,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f820,f87])).

fof(f820,plain,(
    sK3 = k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f819,f788])).

fof(f788,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f787,f100])).

fof(f100,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f38])).

fof(f38,plain,
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

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f787,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f786,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f786,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f785,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f785,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f783,f752])).

fof(f752,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f688,f734])).

fof(f734,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f733,f438])).

fof(f438,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f76,f51])).

fof(f733,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f731,f229])).

fof(f229,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f82,f51])).

fof(f731,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f688,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f687,f419])).

fof(f419,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f305,f415])).

fof(f415,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f410,f53])).

fof(f53,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f410,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f305,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f304,f100])).

fof(f304,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f303,f49])).

fof(f303,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f687,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) ),
    inference(forward_demodulation,[],[f686,f319])).

fof(f319,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f318,f100])).

fof(f318,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f317,f49])).

fof(f317,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f686,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) ),
    inference(subsumption_resolution,[],[f684,f100])).

fof(f684,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f297,f49])).

fof(f297,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f295,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f295,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f59,f61])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f783,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f782,f54])).

fof(f54,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f782,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f781,f100])).

fof(f781,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f780,f49])).

fof(f780,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f744,f61])).

fof(f744,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f425,f734])).

fof(f425,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f336,f415])).

fof(f336,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f321,f334])).

fof(f334,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f331,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f74,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f331,plain,(
    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f330,f100])).

fof(f330,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f329,f49])).

fof(f329,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f320,f60])).

fof(f320,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) ),
    inference(backward_demodulation,[],[f309,f319])).

fof(f309,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f56,f305])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f321,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f307,f319])).

fof(f307,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f58,f305])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f819,plain,(
    sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f818,f96])).

fof(f818,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(forward_demodulation,[],[f794,f87])).

fof(f794,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f118,f788])).

fof(f118,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK1,sK2) ),
    inference(resolution,[],[f68,f97])).

fof(f97,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f69,f51])).

fof(f867,plain,(
    k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f866,f96])).

fof(f866,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f865,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f865,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f806,f821])).

fof(f806,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f427,f788])).

fof(f427,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f424,f415])).

fof(f424,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f335,f415])).

fof(f335,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(resolution,[],[f331,f68])).

fof(f881,plain,(
    ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f880,f55])).

fof(f880,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f879,f870])).

fof(f879,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f873,f822])).

fof(f822,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f49,f821])).

fof(f873,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f842,f870])).

fof(f842,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f841,f821])).

fof(f841,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f834,f821])).

fof(f834,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f816,f821])).

fof(f816,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f815,f788])).

fof(f815,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f792,f88])).

fof(f792,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f54,f788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17199)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (17204)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (17196)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (17199)Refutation not found, incomplete strategy% (17199)------------------------------
% 0.21/0.50  % (17199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17194)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (17197)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (17212)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (17202)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (17194)Refutation not found, incomplete strategy% (17194)------------------------------
% 0.21/0.51  % (17194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17198)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (17199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17199)Memory used [KB]: 10618
% 0.21/0.51  % (17199)Time elapsed: 0.096 s
% 0.21/0.51  % (17199)------------------------------
% 0.21/0.51  % (17199)------------------------------
% 0.21/0.51  % (17206)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (17214)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (17207)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (17195)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (17217)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (17216)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (17208)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (17210)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (17200)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (17194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17194)Memory used [KB]: 10746
% 0.21/0.52  % (17194)Time elapsed: 0.096 s
% 0.21/0.52  % (17194)------------------------------
% 0.21/0.52  % (17194)------------------------------
% 0.21/0.52  % (17218)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (17203)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (17215)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (17205)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (17193)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (17201)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (17213)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (17196)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f883,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f882,f536])).
% 0.21/0.53  fof(f536,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f535,f228])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(X0,k1_xboole_0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f82,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(definition_folding,[],[f35,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f534])).
% 0.21/0.53  fof(f534,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f89,f442])).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f437,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f130,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(resolution,[],[f68,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f69,f55])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f74,f55])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f122,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f77,f55])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f437,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f76,f55])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f36])).
% 0.21/0.54  fof(f882,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.21/0.54    inference(forward_demodulation,[],[f881,f870])).
% 0.21/0.54  fof(f870,plain,(
% 0.21/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f869,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(flattening,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f869,plain,(
% 0.21/0.54    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f868,f132])).
% 0.21/0.54  fof(f868,plain,(
% 0.21/0.54    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK2,k1_relat_1(k1_xboole_0))),
% 0.21/0.54    inference(forward_demodulation,[],[f867,f821])).
% 0.21/0.54  fof(f821,plain,(
% 0.21/0.54    k1_xboole_0 = sK3),
% 0.21/0.54    inference(forward_demodulation,[],[f820,f87])).
% 0.21/0.54  fof(f820,plain,(
% 0.21/0.54    sK3 = k2_zfmisc_1(sK1,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f819,f788])).
% 0.21/0.54  fof(f788,plain,(
% 0.21/0.54    k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f787,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f74,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.54  fof(f787,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f786,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f786,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f785,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f785,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f783,f752])).
% 0.21/0.54  fof(f752,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f688,f734])).
% 0.21/0.54  fof(f734,plain,(
% 0.21/0.54    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f733,f438])).
% 0.21/0.54  fof(f438,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.54    inference(resolution,[],[f76,f51])).
% 0.21/0.54  fof(f733,plain,(
% 0.21/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f731,f229])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    sP0(sK1,sK3,sK2)),
% 0.21/0.54    inference(resolution,[],[f82,f51])).
% 0.21/0.54  fof(f731,plain,(
% 0.21/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~sP0(sK1,sK3,sK2)),
% 0.21/0.54    inference(resolution,[],[f78,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f688,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 0.21/0.54    inference(forward_demodulation,[],[f687,f419])).
% 0.21/0.54  fof(f419,plain,(
% 0.21/0.54    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f305,f415])).
% 0.21/0.54  fof(f415,plain,(
% 0.21/0.54    sK2 = k2_relat_1(sK3)),
% 0.21/0.54    inference(forward_demodulation,[],[f410,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f75,f51])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f304,f100])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f303,f49])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f62,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    v2_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.54  fof(f687,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3))))),
% 0.21/0.54    inference(forward_demodulation,[],[f686,f319])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f318,f100])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f317,f49])).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f63,f52])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f686,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3)))))),
% 0.21/0.54    inference(subsumption_resolution,[],[f684,f100])).
% 0.21/0.54  fof(f684,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k2_relat_1(k2_funct_1(sK3))))) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f297,f49])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f295,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f59,f61])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.54  fof(f783,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(resolution,[],[f782,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f782,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f781,f100])).
% 0.21/0.54  fof(f781,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f780,f49])).
% 0.21/0.54  fof(f780,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f744,f61])).
% 0.21/0.54  fof(f744,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK3)) | v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f425,f734])).
% 0.21/0.54  fof(f425,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f336,f415])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f321,f334])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(resolution,[],[f331,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f74,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f330,f100])).
% 0.21/0.54  fof(f330,plain,(
% 0.21/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f329,f49])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f320,f60])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    ~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))),
% 0.21/0.54    inference(backward_demodulation,[],[f309,f319])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(superposition,[],[f56,f305])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f307,f319])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(superposition,[],[f58,f305])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f819,plain,(
% 0.21/0.54    sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f818,f96])).
% 0.21/0.54  fof(f818,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f794,f87])).
% 0.21/0.54  fof(f794,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.54    inference(backward_demodulation,[],[f118,f788])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) | sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f68,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.54    inference(resolution,[],[f69,f51])).
% 0.21/0.54  fof(f867,plain,(
% 0.21/0.54    k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 0.21/0.54    inference(subsumption_resolution,[],[f866,f96])).
% 0.21/0.54  fof(f866,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f865,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f865,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f806,f821])).
% 0.21/0.54  fof(f806,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f427,f788])).
% 0.21/0.54  fof(f427,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(sK2,k1_relat_1(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f424,f415])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(sK2,k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f335,f415])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    ~r1_tarski(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)),k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))),
% 0.21/0.54    inference(resolution,[],[f331,f68])).
% 0.21/0.54  fof(f881,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f880,f55])).
% 0.21/0.54  fof(f880,plain,(
% 0.21/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.54    inference(forward_demodulation,[],[f879,f870])).
% 0.21/0.54  fof(f879,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f873,f822])).
% 0.21/0.54  fof(f822,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0)),
% 0.21/0.54    inference(backward_demodulation,[],[f49,f821])).
% 0.21/0.54  fof(f873,plain,(
% 0.21/0.54    ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f842,f870])).
% 0.21/0.54  fof(f842,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.54    inference(forward_demodulation,[],[f841,f821])).
% 0.21/0.54  fof(f841,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    inference(forward_demodulation,[],[f834,f821])).
% 0.21/0.54  fof(f834,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    inference(backward_demodulation,[],[f816,f821])).
% 0.21/0.54  fof(f816,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f815,f788])).
% 0.21/0.54  fof(f815,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(forward_demodulation,[],[f792,f88])).
% 0.21/0.54  fof(f792,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.21/0.54    inference(backward_demodulation,[],[f54,f788])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (17196)------------------------------
% 0.21/0.54  % (17196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17196)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (17196)Memory used [KB]: 6524
% 0.21/0.54  % (17196)Time elapsed: 0.126 s
% 0.21/0.54  % (17196)------------------------------
% 0.21/0.54  % (17196)------------------------------
% 0.21/0.54  % (17192)Success in time 0.176 s
%------------------------------------------------------------------------------
