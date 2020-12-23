%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:49 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  158 (2099 expanded)
%              Number of leaves         :   21 ( 509 expanded)
%              Depth                    :   24
%              Number of atoms          :  489 (10688 expanded)
%              Number of equality atoms :  136 ( 517 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f755,plain,(
    $false ),
    inference(subsumption_resolution,[],[f754,f168])).

fof(f168,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f165,f129])).

fof(f129,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f127,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f92,f69])).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f127,plain,(
    v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f126,f124])).

fof(f124,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f119,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f119,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f72,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f75,f69])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f165,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(resolution,[],[f116,f119])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f754,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f753,f129])).

fof(f753,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f752,f568])).

fof(f568,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f217,f565])).

fof(f565,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f563,f165])).

fof(f563,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f562,f228])).

fof(f228,plain,
    ( sK1 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f227,f175])).

fof(f175,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2) ),
    inference(resolution,[],[f94,f67])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f55])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
        | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f227,plain,
    ( sK1 = k1_relset_1(sK1,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f223,f155])).

fof(f155,plain,(
    sP0(sK1,sK2,sK1) ),
    inference(resolution,[],[f100,f67])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f46,f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f223,plain,
    ( sK1 = k1_relset_1(sK1,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ sP0(sK1,sK2,sK1) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f562,plain,(
    ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f561,f165])).

fof(f561,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f507,f557])).

fof(f557,plain,(
    k6_relat_1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) ),
    inference(resolution,[],[f553,f317])).

fof(f317,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(forward_demodulation,[],[f316,f259])).

fof(f259,plain,(
    k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f258,f64])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f258,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f257,f65])).

fof(f257,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f256,f67])).

fof(f256,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f84,f66])).

fof(f66,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f316,plain,(
    m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f315,f67])).

fof(f315,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f314,f66])).

fof(f314,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f312,f65])).

fof(f312,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,X0,X0)
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f88,f64])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f553,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK1) = k1_partfun1(X0,X1,sK1,sK1,k2_funct_1(sK2),sK2) ) ),
    inference(resolution,[],[f500,f67])).

fof(f500,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK1) = k1_partfun1(X2,X3,X0,X1,k2_funct_1(sK2),sK2)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(forward_demodulation,[],[f497,f207])).

fof(f207,plain,(
    k6_relat_1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f189,f206])).

fof(f206,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f140])).

fof(f140,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f93,f67])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f205,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f144])).

fof(f144,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f95,f67])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f204,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f203,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f203,plain,(
    v2_funct_2(sK2,sK1) ),
    inference(subsumption_resolution,[],[f202,f67])).

fof(f202,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f201,f66])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(sK2,X0,X1)
      | v2_funct_2(sK2,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f105,f64])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f189,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f188,f140])).

fof(f188,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f186,f64])).

fof(f186,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f185,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f185,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f184,f67])).

fof(f184,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f183,f66])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(sK2,X0,X1)
      | v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f104,f64])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f497,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(X2,X3,X0,X1,k2_funct_1(sK2),sK2) ) ),
    inference(resolution,[],[f398,f64])).

fof(f398,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k1_partfun1(X8,X9,X6,X7,k2_funct_1(sK2),X5) = k5_relat_1(k2_funct_1(sK2),X5) ) ),
    inference(resolution,[],[f107,f261])).

fof(f261,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f251,f259])).

fof(f251,plain,(
    v1_funct_1(k2_funct_2(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f250,f67])).

fof(f250,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_funct_1(k2_funct_2(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f249,f66])).

fof(f249,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_funct_1(k2_funct_2(sK1,sK2)) ),
    inference(resolution,[],[f248,f65])).

fof(f248,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,X0,X0)
      | ~ v3_funct_2(sK2,X0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,sK2)) ) ),
    inference(resolution,[],[f85,f64])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f507,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f266,f503])).

fof(f503,plain,(
    k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f421,f317])).

fof(f421,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(sK1,sK1,X0,X1,sK2,k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f405,f67])).

fof(f405,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(X6,X7,X4,X5,sK2,k2_funct_1(sK2)) ) ),
    inference(forward_demodulation,[],[f403,f191])).

fof(f191,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f190,f140])).

fof(f190,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f187,f64])).

fof(f187,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f185,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f403,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(X6,X7,X4,X5,sK2,k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f397,f261])).

fof(f397,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f107,f64])).

fof(f266,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f260,f259])).

fof(f260,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f118,f259])).

fof(f118,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f117,f70])).

fof(f117,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) ),
    inference(backward_demodulation,[],[f68,f70])).

fof(f68,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f217,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f214,f140])).

fof(f214,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f74,f206])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f752,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f653,f129])).

fof(f653,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f562,f565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (23415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (23428)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (23444)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (23432)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (23423)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (23436)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (23417)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.52  % (23424)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.52  % (23437)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.52  % (23439)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.52  % (23429)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.52  % (23420)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.53  % (23431)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (23422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (23442)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.53  % (23419)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (23441)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.53  % (23440)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.53  % (23418)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (23435)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.53  % (23433)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.53  % (23416)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.54  % (23427)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.54  % (23421)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.54  % (23443)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (23434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  % (23426)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.54  % (23425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.54  % (23438)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (23430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.58  % (23422)Refutation found. Thanks to Tanya!
% 1.41/0.58  % SZS status Theorem for theBenchmark
% 1.41/0.60  % SZS output start Proof for theBenchmark
% 1.41/0.60  fof(f755,plain,(
% 1.41/0.60    $false),
% 1.41/0.60    inference(subsumption_resolution,[],[f754,f168])).
% 1.41/0.60  fof(f168,plain,(
% 1.41/0.60    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.41/0.60    inference(superposition,[],[f165,f129])).
% 1.41/0.60  fof(f129,plain,(
% 1.41/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.41/0.60    inference(resolution,[],[f127,f122])).
% 1.41/0.60  fof(f122,plain,(
% 1.41/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.41/0.60    inference(resolution,[],[f92,f69])).
% 1.41/0.60  fof(f69,plain,(
% 1.41/0.60    v1_xboole_0(k1_xboole_0)),
% 1.41/0.60    inference(cnf_transformation,[],[f1])).
% 1.41/0.60  fof(f1,axiom,(
% 1.41/0.60    v1_xboole_0(k1_xboole_0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.60  fof(f92,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f41])).
% 1.41/0.60  fof(f41,plain,(
% 1.41/0.60    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f2])).
% 1.41/0.60  fof(f2,axiom,(
% 1.41/0.60    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.41/0.60  fof(f127,plain,(
% 1.41/0.60    v1_xboole_0(k6_relat_1(k1_xboole_0))),
% 1.41/0.60    inference(resolution,[],[f126,f124])).
% 1.41/0.60  fof(f124,plain,(
% 1.41/0.60    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.41/0.60    inference(superposition,[],[f119,f109])).
% 1.41/0.60  fof(f109,plain,(
% 1.41/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.60    inference(equality_resolution,[],[f91])).
% 1.41/0.60  fof(f91,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.41/0.60    inference(cnf_transformation,[],[f60])).
% 1.41/0.60  fof(f60,plain,(
% 1.41/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.60    inference(flattening,[],[f59])).
% 1.41/0.60  fof(f59,plain,(
% 1.41/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.60    inference(nnf_transformation,[],[f3])).
% 1.41/0.60  fof(f3,axiom,(
% 1.41/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.60  fof(f119,plain,(
% 1.41/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.41/0.60    inference(forward_demodulation,[],[f72,f70])).
% 1.41/0.60  fof(f70,plain,(
% 1.41/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f20])).
% 1.41/0.60  fof(f20,axiom,(
% 1.41/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.41/0.60  fof(f72,plain,(
% 1.41/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f24])).
% 1.41/0.60  fof(f24,plain,(
% 1.41/0.60    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.41/0.60    inference(pure_predicate_removal,[],[f17])).
% 1.41/0.60  fof(f17,axiom,(
% 1.41/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.41/0.60  fof(f126,plain,(
% 1.41/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.41/0.60    inference(resolution,[],[f75,f69])).
% 1.41/0.60  fof(f75,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f29])).
% 1.41/0.60  fof(f29,plain,(
% 1.41/0.60    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f4])).
% 1.41/0.60  fof(f4,axiom,(
% 1.41/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.41/0.60  fof(f165,plain,(
% 1.41/0.60    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.41/0.60    inference(resolution,[],[f116,f119])).
% 1.41/0.60  fof(f116,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 1.41/0.60    inference(condensation,[],[f106])).
% 1.41/0.60  fof(f106,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f50])).
% 1.41/0.60  fof(f50,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(flattening,[],[f49])).
% 1.41/0.60  fof(f49,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.41/0.60    inference(ennf_transformation,[],[f12])).
% 1.41/0.60  fof(f12,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.41/0.60  fof(f754,plain,(
% 1.41/0.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.41/0.60    inference(forward_demodulation,[],[f753,f129])).
% 1.41/0.60  fof(f753,plain,(
% 1.41/0.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.41/0.60    inference(forward_demodulation,[],[f752,f568])).
% 1.41/0.60  fof(f568,plain,(
% 1.41/0.60    k1_xboole_0 = k1_relat_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f217,f565])).
% 1.41/0.60  fof(f565,plain,(
% 1.41/0.60    k1_xboole_0 = sK1),
% 1.41/0.60    inference(subsumption_resolution,[],[f563,f165])).
% 1.41/0.60  fof(f563,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) | k1_xboole_0 = sK1),
% 1.41/0.60    inference(superposition,[],[f562,f228])).
% 1.41/0.60  fof(f228,plain,(
% 1.41/0.60    sK1 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.41/0.60    inference(superposition,[],[f227,f175])).
% 1.41/0.60  fof(f175,plain,(
% 1.41/0.60    k1_relat_1(sK2) = k1_relset_1(sK1,sK1,sK2)),
% 1.41/0.60    inference(resolution,[],[f94,f67])).
% 1.41/0.60  fof(f67,plain,(
% 1.41/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(cnf_transformation,[],[f56])).
% 1.41/0.60  fof(f56,plain,(
% 1.41/0.60    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 1.41/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f55])).
% 1.41/0.60  fof(f55,plain,(
% 1.41/0.60    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 1.41/0.60    introduced(choice_axiom,[])).
% 1.41/0.60  fof(f27,plain,(
% 1.41/0.60    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.41/0.60    inference(flattening,[],[f26])).
% 1.41/0.60  fof(f26,plain,(
% 1.41/0.60    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.41/0.60    inference(ennf_transformation,[],[f23])).
% 1.41/0.60  fof(f23,negated_conjecture,(
% 1.41/0.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.41/0.60    inference(negated_conjecture,[],[f22])).
% 1.41/0.60  fof(f22,conjecture,(
% 1.41/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 1.41/0.60  fof(f94,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f43])).
% 1.41/0.60  fof(f43,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(ennf_transformation,[],[f11])).
% 1.41/0.60  fof(f11,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.60  fof(f227,plain,(
% 1.41/0.60    sK1 = k1_relset_1(sK1,sK1,sK2) | k1_xboole_0 = sK1),
% 1.41/0.60    inference(subsumption_resolution,[],[f223,f155])).
% 1.41/0.60  fof(f155,plain,(
% 1.41/0.60    sP0(sK1,sK2,sK1)),
% 1.41/0.60    inference(resolution,[],[f100,f67])).
% 1.41/0.60  fof(f100,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f63])).
% 1.41/0.60  fof(f63,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(nnf_transformation,[],[f54])).
% 1.41/0.60  fof(f54,plain,(
% 1.41/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(definition_folding,[],[f46,f53])).
% 1.41/0.60  fof(f53,plain,(
% 1.41/0.60    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.41/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.60  fof(f46,plain,(
% 1.41/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(flattening,[],[f45])).
% 1.41/0.60  fof(f45,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(ennf_transformation,[],[f14])).
% 1.41/0.60  fof(f14,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.60  fof(f223,plain,(
% 1.41/0.60    sK1 = k1_relset_1(sK1,sK1,sK2) | k1_xboole_0 = sK1 | ~sP0(sK1,sK2,sK1)),
% 1.41/0.60    inference(resolution,[],[f96,f65])).
% 1.41/0.60  fof(f65,plain,(
% 1.41/0.60    v1_funct_2(sK2,sK1,sK1)),
% 1.41/0.60    inference(cnf_transformation,[],[f56])).
% 1.41/0.60  fof(f96,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f62])).
% 1.41/0.60  fof(f62,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.41/0.60    inference(rectify,[],[f61])).
% 1.41/0.60  fof(f61,plain,(
% 1.41/0.60    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.41/0.60    inference(nnf_transformation,[],[f53])).
% 1.41/0.60  fof(f562,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))),
% 1.41/0.60    inference(subsumption_resolution,[],[f561,f165])).
% 1.41/0.60  fof(f561,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))),
% 1.41/0.60    inference(backward_demodulation,[],[f507,f557])).
% 1.41/0.60  fof(f557,plain,(
% 1.41/0.60    k6_relat_1(sK1) = k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2)),
% 1.41/0.60    inference(resolution,[],[f553,f317])).
% 1.41/0.60  fof(f317,plain,(
% 1.41/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(forward_demodulation,[],[f316,f259])).
% 1.41/0.60  fof(f259,plain,(
% 1.41/0.60    k2_funct_2(sK1,sK2) = k2_funct_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f258,f64])).
% 1.41/0.60  fof(f64,plain,(
% 1.41/0.60    v1_funct_1(sK2)),
% 1.41/0.60    inference(cnf_transformation,[],[f56])).
% 1.41/0.60  fof(f258,plain,(
% 1.41/0.60    k2_funct_2(sK1,sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f257,f65])).
% 1.41/0.60  fof(f257,plain,(
% 1.41/0.60    k2_funct_2(sK1,sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,sK1,sK1) | ~v1_funct_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f256,f67])).
% 1.41/0.60  fof(f256,plain,(
% 1.41/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,sK1,sK1) | ~v1_funct_1(sK2)),
% 1.41/0.60    inference(resolution,[],[f84,f66])).
% 1.41/0.60  fof(f66,plain,(
% 1.41/0.60    v3_funct_2(sK2,sK1,sK1)),
% 1.41/0.60    inference(cnf_transformation,[],[f56])).
% 1.41/0.60  fof(f84,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f38])).
% 1.41/0.60  fof(f38,plain,(
% 1.41/0.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.41/0.60    inference(flattening,[],[f37])).
% 1.41/0.60  fof(f37,plain,(
% 1.41/0.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.41/0.60    inference(ennf_transformation,[],[f19])).
% 1.41/0.60  fof(f19,axiom,(
% 1.41/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.41/0.60  fof(f316,plain,(
% 1.41/0.60    m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(subsumption_resolution,[],[f315,f67])).
% 1.41/0.60  fof(f315,plain,(
% 1.41/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(subsumption_resolution,[],[f314,f66])).
% 1.41/0.60  fof(f314,plain,(
% 1.41/0.60    ~v3_funct_2(sK2,sK1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(resolution,[],[f312,f65])).
% 1.41/0.60  fof(f312,plain,(
% 1.41/0.60    ( ! [X0] : (~v1_funct_2(sK2,X0,X0) | ~v3_funct_2(sK2,X0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.41/0.60    inference(resolution,[],[f88,f64])).
% 1.41/0.60  fof(f88,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f40])).
% 1.41/0.60  fof(f40,plain,(
% 1.41/0.60    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.41/0.60    inference(flattening,[],[f39])).
% 1.41/0.60  fof(f39,plain,(
% 1.41/0.60    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.41/0.60    inference(ennf_transformation,[],[f16])).
% 1.41/0.60  fof(f16,axiom,(
% 1.41/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.41/0.60  fof(f553,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK1) = k1_partfun1(X0,X1,sK1,sK1,k2_funct_1(sK2),sK2)) )),
% 1.41/0.60    inference(resolution,[],[f500,f67])).
% 1.41/0.60  fof(f500,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK1) = k1_partfun1(X2,X3,X0,X1,k2_funct_1(sK2),sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.41/0.60    inference(forward_demodulation,[],[f497,f207])).
% 1.41/0.60  fof(f207,plain,(
% 1.41/0.60    k6_relat_1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.41/0.60    inference(backward_demodulation,[],[f189,f206])).
% 1.41/0.60  fof(f206,plain,(
% 1.41/0.60    sK1 = k2_relat_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f205,f140])).
% 1.41/0.60  fof(f140,plain,(
% 1.41/0.60    v1_relat_1(sK2)),
% 1.41/0.60    inference(resolution,[],[f93,f67])).
% 1.41/0.60  fof(f93,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f42])).
% 1.41/0.60  fof(f42,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(ennf_transformation,[],[f8])).
% 1.41/0.60  fof(f8,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.60  fof(f205,plain,(
% 1.41/0.60    sK1 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f204,f144])).
% 1.41/0.60  fof(f144,plain,(
% 1.41/0.60    v5_relat_1(sK2,sK1)),
% 1.41/0.60    inference(resolution,[],[f95,f67])).
% 1.41/0.60  fof(f95,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f44])).
% 1.41/0.60  fof(f44,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(ennf_transformation,[],[f25])).
% 1.41/0.60  fof(f25,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.41/0.60    inference(pure_predicate_removal,[],[f9])).
% 1.41/0.60  fof(f9,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.41/0.60  fof(f204,plain,(
% 1.41/0.60    sK1 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(resolution,[],[f203,f82])).
% 1.41/0.60  fof(f82,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f58])).
% 1.41/0.60  fof(f58,plain,(
% 1.41/0.60    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.60    inference(nnf_transformation,[],[f36])).
% 1.41/0.60  fof(f36,plain,(
% 1.41/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.60    inference(flattening,[],[f35])).
% 1.41/0.60  fof(f35,plain,(
% 1.41/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.41/0.60    inference(ennf_transformation,[],[f15])).
% 1.41/0.60  fof(f15,axiom,(
% 1.41/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.41/0.60  fof(f203,plain,(
% 1.41/0.60    v2_funct_2(sK2,sK1)),
% 1.41/0.60    inference(subsumption_resolution,[],[f202,f67])).
% 1.41/0.60  fof(f202,plain,(
% 1.41/0.60    v2_funct_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(resolution,[],[f201,f66])).
% 1.41/0.60  fof(f201,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v3_funct_2(sK2,X0,X1) | v2_funct_2(sK2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.60    inference(resolution,[],[f105,f64])).
% 1.41/0.60  fof(f105,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f48])).
% 1.41/0.60  fof(f48,plain,(
% 1.41/0.60    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(flattening,[],[f47])).
% 1.41/0.60  fof(f47,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.60    inference(ennf_transformation,[],[f13])).
% 1.41/0.60  fof(f13,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.41/0.60  fof(f189,plain,(
% 1.41/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 1.41/0.60    inference(subsumption_resolution,[],[f188,f140])).
% 1.41/0.60  fof(f188,plain,(
% 1.41/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f186,f64])).
% 1.41/0.60  fof(f186,plain,(
% 1.41/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(resolution,[],[f185,f80])).
% 1.41/0.60  fof(f80,plain,(
% 1.41/0.60    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f33])).
% 1.41/0.60  fof(f33,plain,(
% 1.41/0.60    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.60    inference(flattening,[],[f32])).
% 1.41/0.60  fof(f32,plain,(
% 1.41/0.60    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.60    inference(ennf_transformation,[],[f6])).
% 1.41/0.60  fof(f6,axiom,(
% 1.41/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.41/0.60  fof(f185,plain,(
% 1.41/0.60    v2_funct_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f184,f67])).
% 1.41/0.60  fof(f184,plain,(
% 1.41/0.60    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.60    inference(resolution,[],[f183,f66])).
% 1.41/0.60  fof(f183,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v3_funct_2(sK2,X0,X1) | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.60    inference(resolution,[],[f104,f64])).
% 1.41/0.60  fof(f104,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f48])).
% 1.41/0.60  fof(f497,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(X2,X3,X0,X1,k2_funct_1(sK2),sK2)) )),
% 1.41/0.60    inference(resolution,[],[f398,f64])).
% 1.41/0.60  fof(f398,plain,(
% 1.41/0.60    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_partfun1(X8,X9,X6,X7,k2_funct_1(sK2),X5) = k5_relat_1(k2_funct_1(sK2),X5)) )),
% 1.41/0.60    inference(resolution,[],[f107,f261])).
% 1.41/0.60  fof(f261,plain,(
% 1.41/0.60    v1_funct_1(k2_funct_1(sK2))),
% 1.41/0.60    inference(backward_demodulation,[],[f251,f259])).
% 1.41/0.60  fof(f251,plain,(
% 1.41/0.60    v1_funct_1(k2_funct_2(sK1,sK2))),
% 1.41/0.60    inference(subsumption_resolution,[],[f250,f67])).
% 1.41/0.60  fof(f250,plain,(
% 1.41/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | v1_funct_1(k2_funct_2(sK1,sK2))),
% 1.41/0.60    inference(subsumption_resolution,[],[f249,f66])).
% 1.41/0.60  fof(f249,plain,(
% 1.41/0.60    ~v3_funct_2(sK2,sK1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | v1_funct_1(k2_funct_2(sK1,sK2))),
% 1.41/0.60    inference(resolution,[],[f248,f65])).
% 1.41/0.60  fof(f248,plain,(
% 1.41/0.60    ( ! [X0] : (~v1_funct_2(sK2,X0,X0) | ~v3_funct_2(sK2,X0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,sK2))) )),
% 1.41/0.60    inference(resolution,[],[f85,f64])).
% 1.41/0.60  fof(f85,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f40])).
% 1.41/0.60  fof(f107,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f52])).
% 1.41/0.60  fof(f52,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.41/0.60    inference(flattening,[],[f51])).
% 1.41/0.60  fof(f51,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.41/0.60    inference(ennf_transformation,[],[f18])).
% 1.41/0.60  fof(f18,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.41/0.60  fof(f507,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))),
% 1.41/0.60    inference(backward_demodulation,[],[f266,f503])).
% 1.41/0.60  fof(f503,plain,(
% 1.41/0.60    k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2))),
% 1.41/0.60    inference(resolution,[],[f421,f317])).
% 1.41/0.60  fof(f421,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(sK1,sK1,X0,X1,sK2,k2_funct_1(sK2))) )),
% 1.41/0.60    inference(resolution,[],[f405,f67])).
% 1.41/0.60  fof(f405,plain,(
% 1.41/0.60    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(X6,X7,X4,X5,sK2,k2_funct_1(sK2))) )),
% 1.41/0.60    inference(forward_demodulation,[],[f403,f191])).
% 1.41/0.60  fof(f191,plain,(
% 1.41/0.60    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 1.41/0.60    inference(subsumption_resolution,[],[f190,f140])).
% 1.41/0.60  fof(f190,plain,(
% 1.41/0.60    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f187,f64])).
% 1.41/0.60  fof(f187,plain,(
% 1.41/0.60    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(resolution,[],[f185,f79])).
% 1.41/0.60  fof(f79,plain,(
% 1.41/0.60    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f33])).
% 1.41/0.60  fof(f403,plain,(
% 1.41/0.60    ( ! [X6,X4,X7,X5] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(X6,X7,X4,X5,sK2,k2_funct_1(sK2))) )),
% 1.41/0.60    inference(resolution,[],[f397,f261])).
% 1.41/0.60  fof(f397,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.41/0.60    inference(resolution,[],[f107,f64])).
% 1.41/0.60  fof(f266,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_relat_1(sK1))),
% 1.41/0.60    inference(forward_demodulation,[],[f260,f259])).
% 1.41/0.60  fof(f260,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_relat_1(sK1))),
% 1.41/0.60    inference(backward_demodulation,[],[f118,f259])).
% 1.41/0.60  fof(f118,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_relat_1(sK1))),
% 1.41/0.60    inference(forward_demodulation,[],[f117,f70])).
% 1.41/0.60  fof(f117,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))),
% 1.41/0.60    inference(backward_demodulation,[],[f68,f70])).
% 1.41/0.60  fof(f68,plain,(
% 1.41/0.60    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 1.41/0.60    inference(cnf_transformation,[],[f56])).
% 1.41/0.60  fof(f217,plain,(
% 1.41/0.60    k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(sK2)),
% 1.41/0.60    inference(subsumption_resolution,[],[f214,f140])).
% 1.41/0.60  fof(f214,plain,(
% 1.41/0.60    k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.41/0.60    inference(superposition,[],[f74,f206])).
% 1.41/0.60  fof(f74,plain,(
% 1.41/0.60    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f57])).
% 1.41/0.60  fof(f57,plain,(
% 1.41/0.60    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.60    inference(nnf_transformation,[],[f28])).
% 1.41/0.60  fof(f28,plain,(
% 1.41/0.60    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f5])).
% 1.41/0.60  fof(f5,axiom,(
% 1.41/0.60    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.41/0.60  fof(f752,plain,(
% 1.41/0.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK2)),k1_xboole_0)),
% 1.41/0.60    inference(forward_demodulation,[],[f653,f129])).
% 1.41/0.60  fof(f653,plain,(
% 1.41/0.60    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k6_relat_1(k1_relat_1(sK2)),k6_relat_1(k1_xboole_0))),
% 1.41/0.60    inference(backward_demodulation,[],[f562,f565])).
% 1.41/0.60  % SZS output end Proof for theBenchmark
% 1.41/0.60  % (23422)------------------------------
% 1.41/0.60  % (23422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.60  % (23422)Termination reason: Refutation
% 1.41/0.60  
% 1.41/0.60  % (23422)Memory used [KB]: 6780
% 1.41/0.60  % (23422)Time elapsed: 0.182 s
% 1.41/0.60  % (23422)------------------------------
% 1.41/0.60  % (23422)------------------------------
% 1.41/0.60  % (23414)Success in time 0.25 s
%------------------------------------------------------------------------------
