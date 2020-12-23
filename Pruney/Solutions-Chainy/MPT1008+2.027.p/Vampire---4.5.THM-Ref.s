%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:12 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  140 (12005 expanded)
%              Number of leaves         :   22 (3666 expanded)
%              Depth                    :   22
%              Number of atoms          :  422 (29690 expanded)
%              Number of equality atoms :  212 (15633 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f899,plain,(
    $false ),
    inference(subsumption_resolution,[],[f898,f685])).

fof(f685,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f665,f71])).

fof(f71,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f665,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f570,f663])).

fof(f663,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f471,f660,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f660,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f659,f425])).

fof(f425,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f218,f218,f218,f218,f218,f218,f218,f424,f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | k2_enumset1(X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f107,f93,f116,f116,f116,f117,f117,f117,f93])).

fof(f117,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f116])).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f116,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f79,f93])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f93,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f424,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f207,f240])).

fof(f240,plain,(
    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f192,f189,f82])).

fof(f189,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f119,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f67,f117])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f49])).

fof(f49,plain,
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

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f192,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f119,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f207,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f192,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f218,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f192,f65,f199,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f81,f117,f117])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f199,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f118,f191])).

fof(f191,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f119,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f118,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f69,f117,f117])).

fof(f69,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f659,plain,(
    ! [X0] : v4_relat_1(k1_relat_1(sK2),X0) ),
    inference(forward_demodulation,[],[f657,f444])).

fof(f444,plain,(
    sK2 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f312,f425])).

fof(f312,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f192,f301,f82])).

fof(f301,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f224,f98])).

fof(f224,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f192,f138,f211,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f211,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f200,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f200,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f190,f191])).

fof(f190,plain,(
    m1_subset_1(k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f119,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f138,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f657,plain,(
    ! [X0] : v4_relat_1(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)),X0) ),
    inference(superposition,[],[f319,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f319,plain,(
    ! [X0,X1] : v4_relat_1(k1_relat_1(k7_relat_1(sK2,k2_zfmisc_1(X0,X1))),X0) ),
    inference(unit_resulting_resolution,[],[f236,f98])).

fof(f236,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k7_relat_1(sK2,X0)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f207,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f471,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f466,f425])).

fof(f466,plain,(
    v1_relat_1(k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f407,f444])).

fof(f407,plain,(
    v1_relat_1(k1_relat_1(k7_relat_1(sK2,k1_xboole_0))) ),
    inference(superposition,[],[f322,f140])).

fof(f322,plain,(
    ! [X0,X1] : v1_relat_1(k1_relat_1(k7_relat_1(sK2,k2_zfmisc_1(X0,X1)))) ),
    inference(unit_resulting_resolution,[],[f236,f95])).

fof(f570,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(k1_xboole_0,X0))) ),
    inference(unit_resulting_resolution,[],[f473,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f473,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X0)),X0) ),
    inference(forward_demodulation,[],[f468,f425])).

fof(f468,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k1_relat_1(sK2),X0)),X0) ),
    inference(backward_demodulation,[],[f413,f444])).

fof(f413,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)),X0)),X0) ),
    inference(unit_resulting_resolution,[],[f407,f80])).

fof(f898,plain,(
    r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f827,f72])).

fof(f72,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f827,plain,(
    r2_hidden(k1_funct_1(k1_xboole_0,sK0),k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f201,f813])).

fof(f813,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f684,f487])).

fof(f487,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f486,f141])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f486,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f485,f425])).

fof(f485,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2) ),
    inference(forward_demodulation,[],[f446,f141])).

fof(f446,plain,
    ( sK2 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2) ),
    inference(backward_demodulation,[],[f315,f425])).

fof(f315,plain,
    ( sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2) ),
    inference(resolution,[],[f305,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f305,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f224,f86])).

fof(f684,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f664,f71])).

fof(f664,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f473,f663])).

fof(f201,plain,(
    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f188,f191])).

fof(f188,plain,(
    r2_hidden(k1_funct_1(sK2,sK0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f145,f120,f119,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f120,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f66,f117])).

fof(f66,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f145,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f101,f116])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f68,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:56:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.47  % (22276)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.48  % (22260)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.51  % (22260)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f899,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(subsumption_resolution,[],[f898,f685])).
% 0.23/0.52  fof(f685,plain,(
% 0.23/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.52    inference(forward_demodulation,[],[f665,f71])).
% 0.23/0.52  fof(f71,plain,(
% 0.23/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.52    inference(cnf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,axiom,(
% 0.23/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.23/0.52  fof(f665,plain,(
% 0.23/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.23/0.52    inference(backward_demodulation,[],[f570,f663])).
% 0.23/0.52  fof(f663,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f471,f660,f82])).
% 0.23/0.52  fof(f82,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f35])).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.52    inference(flattening,[],[f34])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.52    inference(ennf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,axiom,(
% 0.23/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.23/0.52  fof(f660,plain,(
% 0.23/0.52    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.23/0.52    inference(forward_demodulation,[],[f659,f425])).
% 0.23/0.52  fof(f425,plain,(
% 0.23/0.52    k1_xboole_0 = k1_relat_1(sK2)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f218,f218,f218,f218,f218,f218,f218,f424,f137])).
% 0.23/0.52  fof(f137,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k2_enumset1(X0,X0,X1,X2) = X3) )),
% 0.23/0.52    inference(definition_unfolding,[],[f107,f93,f116,f116,f116,f117,f117,f117,f93])).
% 0.23/0.52  fof(f117,plain,(
% 0.23/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.23/0.52    inference(definition_unfolding,[],[f74,f116])).
% 0.23/0.52  fof(f74,plain,(
% 0.23/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.52  fof(f116,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.52    inference(definition_unfolding,[],[f79,f93])).
% 0.23/0.52  fof(f79,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.52  fof(f93,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.52  fof(f107,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f64])).
% 0.23/0.52  fof(f64,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.23/0.52    inference(flattening,[],[f63])).
% 0.23/0.52  fof(f63,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.23/0.52    inference(nnf_transformation,[],[f48])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 0.23/0.52    inference(ennf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 0.23/0.52  fof(f424,plain,(
% 0.23/0.52    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.23/0.52    inference(superposition,[],[f207,f240])).
% 0.23/0.52  fof(f240,plain,(
% 0.23/0.52    sK2 = k7_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f192,f189,f82])).
% 0.23/0.52  fof(f189,plain,(
% 0.23/0.52    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f119,f98])).
% 0.23/0.52  fof(f98,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f43])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f27])).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.23/0.52    inference(pure_predicate_removal,[],[f19])).
% 0.23/0.52  fof(f19,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.52  fof(f119,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.52    inference(definition_unfolding,[],[f67,f117])).
% 0.23/0.52  fof(f67,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.23/0.52    inference(cnf_transformation,[],[f50])).
% 0.23/0.52  fof(f50,plain,(
% 0.23/0.52    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f49])).
% 0.23/0.52  fof(f49,plain,(
% 0.23/0.52    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.23/0.52    inference(flattening,[],[f28])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.23/0.52    inference(ennf_transformation,[],[f26])).
% 0.23/0.52  fof(f26,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.23/0.52    inference(negated_conjecture,[],[f25])).
% 0.23/0.52  fof(f25,conjecture,(
% 0.23/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    v1_relat_1(sK2)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f119,f95])).
% 0.23/0.52  fof(f95,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f40])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f18])).
% 0.23/0.52  fof(f18,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.52  fof(f207,plain,(
% 0.23/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f192,f80])).
% 0.23/0.52  fof(f80,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f31])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,axiom,(
% 0.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.23/0.52  fof(f218,plain,(
% 0.23/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f192,f65,f199,f122])).
% 0.23/0.52  fof(f122,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.52    inference(definition_unfolding,[],[f81,f117,f117])).
% 0.23/0.52  fof(f81,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f33])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.52    inference(flattening,[],[f32])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.52    inference(ennf_transformation,[],[f16])).
% 0.23/0.52  fof(f16,axiom,(
% 0.23/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.23/0.52  fof(f199,plain,(
% 0.23/0.52    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.23/0.52    inference(backward_demodulation,[],[f118,f191])).
% 0.23/0.52  fof(f191,plain,(
% 0.23/0.52    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f119,f96])).
% 0.23/0.52  fof(f96,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f41])).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f21])).
% 0.23/0.52  fof(f21,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.52  fof(f118,plain,(
% 0.23/0.52    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.23/0.52    inference(definition_unfolding,[],[f69,f117,f117])).
% 0.23/0.52  fof(f69,plain,(
% 0.23/0.52    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.23/0.52    inference(cnf_transformation,[],[f50])).
% 0.23/0.52  fof(f65,plain,(
% 0.23/0.52    v1_funct_1(sK2)),
% 0.23/0.52    inference(cnf_transformation,[],[f50])).
% 0.23/0.52  fof(f659,plain,(
% 0.23/0.52    ( ! [X0] : (v4_relat_1(k1_relat_1(sK2),X0)) )),
% 0.23/0.52    inference(forward_demodulation,[],[f657,f444])).
% 0.23/0.52  fof(f444,plain,(
% 0.23/0.52    sK2 = k7_relat_1(sK2,k1_xboole_0)),
% 0.23/0.52    inference(backward_demodulation,[],[f312,f425])).
% 0.23/0.52  fof(f312,plain,(
% 0.23/0.52    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f192,f301,f82])).
% 0.23/0.52  fof(f301,plain,(
% 0.23/0.52    v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f224,f98])).
% 0.23/0.52  fof(f224,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.23/0.52    inference(unit_resulting_resolution,[],[f192,f138,f211,f94])).
% 0.23/0.52  fof(f94,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f39])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(flattening,[],[f38])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f22])).
% 0.23/0.52  fof(f22,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.23/0.53  fof(f211,plain,(
% 0.23/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f200,f86])).
% 0.23/0.53  fof(f86,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f55])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.53    inference(nnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.53  fof(f200,plain,(
% 0.23/0.53    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.23/0.53    inference(forward_demodulation,[],[f190,f191])).
% 0.23/0.53  fof(f190,plain,(
% 0.23/0.53    m1_subset_1(k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2),k1_zfmisc_1(sK1))),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f119,f97])).
% 0.23/0.53  fof(f97,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(ennf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.23/0.53  fof(f138,plain,(
% 0.23/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f84])).
% 0.23/0.53  fof(f84,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f54])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.53    inference(flattening,[],[f53])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.53    inference(nnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.53  fof(f657,plain,(
% 0.23/0.53    ( ! [X0] : (v4_relat_1(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)),X0)) )),
% 0.23/0.53    inference(superposition,[],[f319,f140])).
% 0.23/0.53  fof(f140,plain,(
% 0.23/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.53    inference(equality_resolution,[],[f90])).
% 0.23/0.53  fof(f90,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f57])).
% 0.23/0.53  fof(f57,plain,(
% 0.23/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.53    inference(flattening,[],[f56])).
% 0.23/0.53  fof(f56,plain,(
% 0.23/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.23/0.53    inference(nnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.53  fof(f319,plain,(
% 0.23/0.53    ( ! [X0,X1] : (v4_relat_1(k1_relat_1(k7_relat_1(sK2,k2_zfmisc_1(X0,X1))),X0)) )),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f236,f98])).
% 0.23/0.53  fof(f236,plain,(
% 0.23/0.53    ( ! [X0] : (m1_subset_1(k1_relat_1(k7_relat_1(sK2,X0)),k1_zfmisc_1(X0))) )),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f207,f87])).
% 0.23/0.53  fof(f87,plain,(
% 0.23/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f55])).
% 0.23/0.53  fof(f471,plain,(
% 0.23/0.53    v1_relat_1(k1_xboole_0)),
% 0.23/0.53    inference(forward_demodulation,[],[f466,f425])).
% 0.23/0.53  fof(f466,plain,(
% 0.23/0.53    v1_relat_1(k1_relat_1(sK2))),
% 0.23/0.53    inference(backward_demodulation,[],[f407,f444])).
% 0.23/0.53  fof(f407,plain,(
% 0.23/0.53    v1_relat_1(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)))),
% 0.23/0.53    inference(superposition,[],[f322,f140])).
% 0.23/0.53  fof(f322,plain,(
% 0.23/0.53    ( ! [X0,X1] : (v1_relat_1(k1_relat_1(k7_relat_1(sK2,k2_zfmisc_1(X0,X1))))) )),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f236,f95])).
% 0.23/0.53  fof(f570,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(k1_xboole_0,X0)))) )),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f473,f92])).
% 0.23/0.53  fof(f92,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,axiom,(
% 0.23/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.23/0.53  fof(f473,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X0)),X0)) )),
% 0.23/0.53    inference(forward_demodulation,[],[f468,f425])).
% 0.23/0.53  fof(f468,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k1_relat_1(sK2),X0)),X0)) )),
% 0.23/0.53    inference(backward_demodulation,[],[f413,f444])).
% 0.23/0.53  fof(f413,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)),X0)),X0)) )),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f407,f80])).
% 0.23/0.53  fof(f898,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.23/0.53    inference(forward_demodulation,[],[f827,f72])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f827,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(k1_xboole_0,sK0),k2_relat_1(k1_xboole_0))),
% 0.23/0.53    inference(backward_demodulation,[],[f201,f813])).
% 0.23/0.53  fof(f813,plain,(
% 0.23/0.53    k1_xboole_0 = sK2),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f684,f487])).
% 0.23/0.53  fof(f487,plain,(
% 0.23/0.53    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 0.23/0.53    inference(forward_demodulation,[],[f486,f141])).
% 0.23/0.53  fof(f141,plain,(
% 0.23/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f89])).
% 0.23/0.53  fof(f89,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f57])).
% 0.23/0.53  fof(f486,plain,(
% 0.23/0.53    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2) | k1_xboole_0 = sK2),
% 0.23/0.53    inference(forward_demodulation,[],[f485,f425])).
% 0.23/0.53  fof(f485,plain,(
% 0.23/0.53    k1_xboole_0 = sK2 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2)),
% 0.23/0.53    inference(forward_demodulation,[],[f446,f141])).
% 0.23/0.53  fof(f446,plain,(
% 0.23/0.53    sK2 = k2_zfmisc_1(k1_xboole_0,sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2)),
% 0.23/0.53    inference(backward_demodulation,[],[f315,f425])).
% 0.23/0.53  fof(f315,plain,(
% 0.23/0.53    sK2 = k2_zfmisc_1(k1_relat_1(sK2),sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),sK2)),
% 0.23/0.53    inference(resolution,[],[f305,f85])).
% 0.23/0.53  fof(f85,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f54])).
% 0.23/0.53  fof(f305,plain,(
% 0.23/0.53    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f224,f86])).
% 0.23/0.53  fof(f684,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.53    inference(forward_demodulation,[],[f664,f71])).
% 0.23/0.53  fof(f664,plain,(
% 0.23/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.23/0.53    inference(backward_demodulation,[],[f473,f663])).
% 0.23/0.53  fof(f201,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.23/0.53    inference(forward_demodulation,[],[f188,f191])).
% 0.23/0.53  fof(f188,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(sK2,sK0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f65,f68,f145,f120,f119,f106])).
% 0.23/0.53  fof(f106,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f47])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.23/0.53    inference(flattening,[],[f46])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.23/0.53    inference(ennf_transformation,[],[f24])).
% 0.23/0.53  fof(f24,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.23/0.53  fof(f120,plain,(
% 0.23/0.53    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.23/0.53    inference(definition_unfolding,[],[f66,f117])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f50])).
% 0.23/0.53  fof(f145,plain,(
% 0.23/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 0.23/0.53    inference(equality_resolution,[],[f144])).
% 0.23/0.53  fof(f144,plain,(
% 0.23/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 0.23/0.53    inference(equality_resolution,[],[f127])).
% 0.23/0.53  fof(f127,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.23/0.53    inference(definition_unfolding,[],[f101,f116])).
% 0.23/0.53  fof(f101,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.23/0.53    inference(cnf_transformation,[],[f62])).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.23/0.53    inference(rectify,[],[f59])).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.23/0.53    inference(flattening,[],[f58])).
% 0.23/0.53  fof(f58,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.23/0.53    inference(nnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    k1_xboole_0 != sK1),
% 0.23/0.53    inference(cnf_transformation,[],[f50])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (22260)------------------------------
% 0.23/0.53  % (22260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (22260)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (22260)Memory used [KB]: 6780
% 0.23/0.53  % (22260)Time elapsed: 0.078 s
% 0.23/0.53  % (22260)------------------------------
% 0.23/0.53  % (22260)------------------------------
% 1.27/0.53  % (22248)Success in time 0.155 s
%------------------------------------------------------------------------------
