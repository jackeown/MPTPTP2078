%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 898 expanded)
%              Number of leaves         :   16 ( 224 expanded)
%              Depth                    :   26
%              Number of atoms          :  357 (5765 expanded)
%              Number of equality atoms :  107 (1435 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f913,plain,(
    $false ),
    inference(subsumption_resolution,[],[f912,f750])).

fof(f750,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f647,f726])).

fof(f726,plain,
    ( ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f722,f615])).

fof(f615,plain,
    ( sK5 = k1_relat_1(k7_relat_1(sK6,sK5))
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f175,f52])).

fof(f52,plain,(
    r1_tarski(sK5,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4)
      | ~ v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5)) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_tarski(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4)
        | ~ v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5)) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_tarski(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f175,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | k1_relat_1(k7_relat_1(sK6,X3)) = X3
      | k1_xboole_0 = sK4 ) ),
    inference(subsumption_resolution,[],[f174,f93])).

fof(f93,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f174,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | k1_relat_1(k7_relat_1(sK6,X3)) = X3
      | ~ v1_relat_1(sK6)
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f56,f170])).

fof(f170,plain,
    ( sK3 = k1_relat_1(sK6)
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f156,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f156,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f155,f96])).

fof(f96,plain,(
    sP1(sK3,sK6,sK4) ),
    inference(resolution,[],[f51,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f155,plain,
    ( sK3 = k1_relat_1(sK6)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK6,sK4) ),
    inference(subsumption_resolution,[],[f151,f50])).

fof(f50,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f151,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK6,sK4) ),
    inference(superposition,[],[f94,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f94,plain,(
    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f722,plain,
    ( sK5 != k1_relat_1(k7_relat_1(sK6,sK5))
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f721])).

fof(f721,plain,
    ( sK5 != k1_relat_1(k7_relat_1(sK6,sK5))
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 = sK4
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(superposition,[],[f422,f65])).

fof(f422,plain,
    ( sK5 != k1_relset_1(sK5,sK4,k7_relat_1(sK6,sK5))
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f179,f71])).

fof(f179,plain,
    ( sP0(sK5,sK4)
    | sK5 != k1_relset_1(sK5,sK4,k7_relat_1(sK6,sK5))
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(subsumption_resolution,[],[f176,f73])).

fof(f176,plain,
    ( ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | sK5 != k1_relset_1(sK5,sK4,k7_relat_1(sK6,sK5))
    | sP0(sK5,sK4)
    | ~ sP1(sK5,k7_relat_1(sK6,sK5),sK4) ),
    inference(resolution,[],[f166,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f166,plain,
    ( ~ v1_funct_2(k7_relat_1(sK6,sK5),sK5,sK4)
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(forward_demodulation,[],[f165,f102])).

fof(f102,plain,(
    ! [X1] : k2_partfun1(sK3,sK4,sK6,X1) = k7_relat_1(sK6,X1) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X1] :
      ( k2_partfun1(sK3,sK4,sK6,X1) = k7_relat_1(sK6,X1)
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f165,plain,
    ( ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4) ),
    inference(subsumption_resolution,[],[f164,f144])).

fof(f144,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK6,X0)) ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f143,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK6,X0))
      | ~ v1_funct_1(sK6) ) ),
    inference(subsumption_resolution,[],[f141,f51])).

fof(f141,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK6,X0))
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_1(sK6) ) ),
    inference(superposition,[],[f103,f76])).

fof(f103,plain,(
    ! [X2] : v1_funct_1(k2_partfun1(sK3,sK4,sK6,X2)) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,(
    ! [X2] :
      ( v1_funct_1(k2_partfun1(sK3,sK4,sK6,X2))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f51,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f164,plain,
    ( ~ v1_funct_1(k7_relat_1(sK6,sK5))
    | ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4) ),
    inference(forward_demodulation,[],[f159,f102])).

fof(f159,plain,
    ( ~ m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5))
    | ~ v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4) ),
    inference(backward_demodulation,[],[f54,f102])).

fof(f54,plain,
    ( ~ v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5))
    | ~ v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4)
    | ~ m1_subset_1(k2_partfun1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f647,plain,
    ( m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f619,f615])).

fof(f619,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK6,X0)),sK4))) ),
    inference(resolution,[],[f228,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f228,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK6,X5)),X6)
      | m1_subset_1(k7_relat_1(sK6,X5),k1_zfmisc_1(k2_zfmisc_1(X6,sK4))) ) ),
    inference(resolution,[],[f214,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f28])).

% (22525)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f214,plain,(
    ! [X3] : m1_subset_1(k7_relat_1(sK6,X3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(forward_demodulation,[],[f104,f102])).

fof(f104,plain,(
    ! [X3] : m1_subset_1(k2_partfun1(sK3,sK4,sK6,X3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X3] :
      ( m1_subset_1(k2_partfun1(sK3,sK4,sK6,X3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f51,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f912,plain,(
    k1_xboole_0 != sK4 ),
    inference(subsumption_resolution,[],[f904,f80])).

fof(f904,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK4 ),
    inference(superposition,[],[f891,f53])).

fof(f53,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f891,plain,(
    ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f185,f857])).

fof(f857,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f836,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f836,plain,(
    r1_tarski(sK5,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f759])).

fof(f759,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f112,f750])).

fof(f112,plain,
    ( k1_xboole_0 != sK4
    | r1_tarski(sK5,k1_xboole_0) ),
    inference(superposition,[],[f52,f53])).

fof(f185,plain,(
    ~ r1_tarski(sK3,sK5) ),
    inference(subsumption_resolution,[],[f184,f51])).

fof(f184,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK3,sK5) ),
    inference(forward_demodulation,[],[f183,f108])).

fof(f108,plain,(
    sK6 = k7_relat_1(sK6,sK3) ),
    inference(subsumption_resolution,[],[f107,f93])).

fof(f107,plain,
    ( sK6 = k7_relat_1(sK6,sK3)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f95,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f95,plain,(
    v4_relat_1(sK6,sK3) ),
    inference(resolution,[],[f51,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f183,plain,
    ( ~ m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK3,sK5) ),
    inference(subsumption_resolution,[],[f182,f50])).

fof(f182,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | ~ m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK3,sK5) ),
    inference(forward_demodulation,[],[f178,f108])).

fof(f178,plain,
    ( ~ v1_funct_2(k7_relat_1(sK6,sK3),sK3,sK4)
    | ~ m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK3,sK5) ),
    inference(superposition,[],[f166,f90])).

fof(f90,plain,
    ( sK3 = sK5
    | ~ r1_tarski(sK3,sK5) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (22521)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (22512)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (22521)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (22524)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f913,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f912,f750])).
% 0.21/0.51  fof(f750,plain,(
% 0.21/0.51    k1_xboole_0 = sK4),
% 0.21/0.51    inference(subsumption_resolution,[],[f647,f726])).
% 0.21/0.51  fof(f726,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 = sK4),
% 0.21/0.51    inference(subsumption_resolution,[],[f722,f615])).
% 0.21/0.51  fof(f615,plain,(
% 0.21/0.51    sK5 = k1_relat_1(k7_relat_1(sK6,sK5)) | k1_xboole_0 = sK4),
% 0.21/0.51    inference(resolution,[],[f175,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    r1_tarski(sK5,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    (~m1_subset_1(k2_partfun1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4) | ~v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5))) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4) | ~v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5))) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ( ! [X3] : (~r1_tarski(X3,sK3) | k1_relat_1(k7_relat_1(sK6,X3)) = X3 | k1_xboole_0 = sK4) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f174,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v1_relat_1(sK6)),
% 0.21/0.51    inference(resolution,[],[f51,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X3] : (~r1_tarski(X3,sK3) | k1_relat_1(k7_relat_1(sK6,X3)) = X3 | ~v1_relat_1(sK6) | k1_xboole_0 = sK4) )),
% 0.21/0.51    inference(superposition,[],[f56,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    sK3 = k1_relat_1(sK6) | k1_xboole_0 = sK4),
% 0.21/0.51    inference(resolution,[],[f156,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    sP1(sK3,sK6,sK4)),
% 0.21/0.51    inference(resolution,[],[f51,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(definition_folding,[],[f27,f36,f35,f34])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    sK3 = k1_relat_1(sK6) | sP0(sK3,sK4) | ~sP1(sK3,sK6,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f151,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    sK3 = k1_relat_1(sK6) | ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK6,sK4)),
% 0.21/0.51    inference(superposition,[],[f94,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f35])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6)),
% 0.21/0.51    inference(resolution,[],[f51,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.51  fof(f722,plain,(
% 0.21/0.51    sK5 != k1_relat_1(k7_relat_1(sK6,sK5)) | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 = sK4),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f721])).
% 0.21/0.51  fof(f721,plain,(
% 0.21/0.51    sK5 != k1_relat_1(k7_relat_1(sK6,sK5)) | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 = sK4 | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.51    inference(superposition,[],[f422,f65])).
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    sK5 != k1_relset_1(sK5,sK4,k7_relat_1(sK6,sK5)) | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 = sK4),
% 0.21/0.51    inference(resolution,[],[f179,f71])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    sP0(sK5,sK4) | sK5 != k1_relset_1(sK5,sK4,k7_relat_1(sK6,sK5)) | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f176,f73])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | sK5 != k1_relset_1(sK5,sK4,k7_relat_1(sK6,sK5)) | sP0(sK5,sK4) | ~sP1(sK5,k7_relat_1(sK6,sK5),sK4)),
% 0.21/0.51    inference(resolution,[],[f166,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK6,sK5),sK5,sK4) | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.51    inference(forward_demodulation,[],[f165,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X1] : (k2_partfun1(sK3,sK4,sK6,X1) = k7_relat_1(sK6,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f99,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_funct_1(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X1] : (k2_partfun1(sK3,sK4,sK6,X1) = k7_relat_1(sK6,X1) | ~v1_funct_1(sK6)) )),
% 0.21/0.51    inference(resolution,[],[f51,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k7_relat_1(sK6,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f49])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k7_relat_1(sK6,X0)) | ~v1_funct_1(sK6)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f51])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k7_relat_1(sK6,X0)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)) )),
% 0.21/0.51    inference(superposition,[],[f103,f76])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X2] : (v1_funct_1(k2_partfun1(sK3,sK4,sK6,X2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f49])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X2] : (v1_funct_1(k2_partfun1(sK3,sK4,sK6,X2)) | ~v1_funct_1(sK6)) )),
% 0.21/0.51    inference(resolution,[],[f51,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~v1_funct_1(k7_relat_1(sK6,sK5)) | ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f159,f102])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5)) | ~v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4)),
% 0.21/0.51    inference(backward_demodulation,[],[f54,f102])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~v1_funct_1(k2_partfun1(sK3,sK4,sK6,sK5)) | ~v1_funct_2(k2_partfun1(sK3,sK4,sK6,sK5),sK5,sK4) | ~m1_subset_1(k2_partfun1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f647,plain,(
% 0.21/0.51    m1_subset_1(k7_relat_1(sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 = sK4),
% 0.21/0.51    inference(superposition,[],[f619,f615])).
% 0.21/0.51  fof(f619,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k7_relat_1(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK6,X0)),sK4)))) )),
% 0.21/0.51    inference(resolution,[],[f228,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~r1_tarski(k1_relat_1(k7_relat_1(sK6,X5)),X6) | m1_subset_1(k7_relat_1(sK6,X5),k1_zfmisc_1(k2_zfmisc_1(X6,sK4)))) )),
% 0.21/0.51    inference(resolution,[],[f214,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  % (22525)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k7_relat_1(sK6,X3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f104,f102])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k2_partfun1(sK3,sK4,sK6,X3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f49])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k2_partfun1(sK3,sK4,sK6,X3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)) )),
% 0.21/0.51    inference(resolution,[],[f51,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f912,plain,(
% 0.21/0.51    k1_xboole_0 != sK4),
% 0.21/0.51    inference(subsumption_resolution,[],[f904,f80])).
% 0.21/0.51  fof(f904,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK4),
% 0.21/0.51    inference(superposition,[],[f891,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f891,plain,(
% 0.21/0.51    ~r1_tarski(sK3,k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f185,f857])).
% 0.21/0.51  fof(f857,plain,(
% 0.21/0.51    k1_xboole_0 = sK5),
% 0.21/0.51    inference(resolution,[],[f836,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.51  fof(f836,plain,(
% 0.21/0.51    r1_tarski(sK5,k1_xboole_0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f759])).
% 0.21/0.51  fof(f759,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK5,k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f112,f750])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    k1_xboole_0 != sK4 | r1_tarski(sK5,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f52,f53])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~r1_tarski(sK3,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f51])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~r1_tarski(sK3,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f183,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    sK6 = k7_relat_1(sK6,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f93])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    sK6 = k7_relat_1(sK6,sK3) | ~v1_relat_1(sK6)),
% 0.21/0.51    inference(resolution,[],[f95,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    v4_relat_1(sK6,sK3)),
% 0.21/0.51    inference(resolution,[],[f51,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~r1_tarski(sK3,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f182,f50])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~v1_funct_2(sK6,sK3,sK4) | ~m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~r1_tarski(sK3,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f178,f108])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK6,sK3),sK3,sK4) | ~m1_subset_1(k7_relat_1(sK6,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~r1_tarski(sK3,sK5)),
% 0.21/0.51    inference(superposition,[],[f166,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    sK3 = sK5 | ~r1_tarski(sK3,sK5)),
% 0.21/0.51    inference(resolution,[],[f52,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (22521)------------------------------
% 0.21/0.51  % (22521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22521)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (22521)Memory used [KB]: 1918
% 0.21/0.51  % (22521)Time elapsed: 0.081 s
% 0.21/0.51  % (22521)------------------------------
% 0.21/0.51  % (22521)------------------------------
% 0.21/0.51  % (22509)Success in time 0.149 s
%------------------------------------------------------------------------------
