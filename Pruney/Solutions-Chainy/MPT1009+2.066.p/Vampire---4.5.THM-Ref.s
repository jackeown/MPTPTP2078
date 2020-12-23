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
% DateTime   : Thu Dec  3 13:04:35 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 363 expanded)
%              Number of leaves         :   22 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          :  312 ( 892 expanded)
%              Number of equality atoms :  134 ( 405 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f199,f227,f261,f374,f391,f430])).

fof(f430,plain,(
    ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f95,f427])).

fof(f427,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(resolution,[],[f409,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f409,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f99,f373])).

fof(f373,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl4_19
  <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f99,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f73,f93])).

fof(f93,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f74,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f73,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f44,f72,f72])).

fof(f44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f391,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f41,f370])).

fof(f370,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl4_18
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f374,plain,
    ( ~ spl4_3
    | ~ spl4_18
    | spl4_19
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f367,f107,f372,f369,f149])).

fof(f149,plain,
    ( spl4_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f107,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f367,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(equality_resolution,[],[f286])).

fof(f286,plain,
    ( ! [X6] :
        ( k1_relat_1(sK3) != k1_relat_1(X6)
        | k2_relat_1(X6) = k2_enumset1(k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0))
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6) )
    | ~ spl4_2 ),
    inference(superposition,[],[f75,f108])).

fof(f108,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f72,f72])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f261,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f260,f107,f104])).

fof(f104,plain,
    ( spl4_1
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f260,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f98,f84])).

fof(f84,plain,(
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
    inference(definition_unfolding,[],[f62,f57,f71,f71,f71,f72,f72,f72,f57])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f98,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(global_subsumption,[],[f95,f97])).

fof(f97,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f94,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f94,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f227,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl4_7 ),
    inference(resolution,[],[f220,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f220,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f216,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f216,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f170,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f170,plain,(
    ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    inference(global_subsumption,[],[f95,f168])).

fof(f168,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f121,f53])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f112,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f112,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0) ),
    inference(resolution,[],[f110,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0) ) ),
    inference(resolution,[],[f99,f60])).

fof(f199,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f191,f104,f197,f149])).

fof(f191,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(superposition,[],[f50,f105])).

% (21233)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f105,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f156,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f95,f150])).

fof(f150,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (21219)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.56  % (21223)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.56  % (21235)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.57  % (21227)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.57  % (21244)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.57  % (21240)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.57  % (21221)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.57  % (21218)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.58  % (21232)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.58  % (21217)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.68/0.58  % (21228)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.68/0.58  % (21226)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.58  % (21222)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.68/0.59  % (21231)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.59  % (21234)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.68/0.59  % (21224)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.68/0.59  % (21234)Refutation not found, incomplete strategy% (21234)------------------------------
% 1.68/0.59  % (21234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (21219)Refutation found. Thanks to Tanya!
% 1.68/0.59  % SZS status Theorem for theBenchmark
% 1.68/0.59  % (21234)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (21234)Memory used [KB]: 10618
% 1.68/0.59  % (21234)Time elapsed: 0.164 s
% 1.68/0.59  % (21234)------------------------------
% 1.68/0.59  % (21234)------------------------------
% 1.68/0.59  % (21238)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.68/0.59  % SZS output start Proof for theBenchmark
% 1.68/0.59  fof(f431,plain,(
% 1.68/0.59    $false),
% 1.68/0.59    inference(avatar_sat_refutation,[],[f156,f199,f227,f261,f374,f391,f430])).
% 1.68/0.59  fof(f430,plain,(
% 1.68/0.59    ~spl4_19),
% 1.68/0.59    inference(avatar_contradiction_clause,[],[f429])).
% 1.68/0.59  fof(f429,plain,(
% 1.68/0.59    $false | ~spl4_19),
% 1.68/0.59    inference(subsumption_resolution,[],[f95,f427])).
% 1.68/0.59  fof(f427,plain,(
% 1.68/0.59    ~v1_relat_1(sK3) | ~spl4_19),
% 1.68/0.59    inference(resolution,[],[f409,f53])).
% 1.68/0.59  fof(f53,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f26])).
% 1.68/0.59  fof(f26,plain,(
% 1.68/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.68/0.59    inference(ennf_transformation,[],[f10])).
% 1.68/0.59  fof(f10,axiom,(
% 1.68/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.68/0.59  fof(f409,plain,(
% 1.68/0.59    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_19),
% 1.68/0.59    inference(backward_demodulation,[],[f99,f373])).
% 1.68/0.59  fof(f373,plain,(
% 1.68/0.59    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_19),
% 1.68/0.59    inference(avatar_component_clause,[],[f372])).
% 1.68/0.59  fof(f372,plain,(
% 1.68/0.59    spl4_19 <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.68/0.59  fof(f99,plain,(
% 1.68/0.59    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.68/0.59    inference(backward_demodulation,[],[f73,f93])).
% 1.68/0.59  fof(f93,plain,(
% 1.68/0.59    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.68/0.59    inference(resolution,[],[f74,f61])).
% 1.68/0.59  fof(f61,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f34])).
% 1.68/0.59  fof(f34,plain,(
% 1.68/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.59    inference(ennf_transformation,[],[f16])).
% 1.68/0.59  fof(f16,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.68/0.59  fof(f74,plain,(
% 1.68/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.68/0.59    inference(definition_unfolding,[],[f42,f72])).
% 1.68/0.59  fof(f72,plain,(
% 1.68/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f49,f71])).
% 1.68/0.59  fof(f71,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f52,f57])).
% 1.68/0.59  fof(f57,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f5])).
% 1.68/0.59  fof(f5,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.59  fof(f52,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f4])).
% 1.68/0.59  fof(f4,axiom,(
% 1.68/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.59  fof(f49,plain,(
% 1.68/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f3])).
% 1.68/0.59  fof(f3,axiom,(
% 1.68/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.59  fof(f42,plain,(
% 1.68/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.68/0.59    inference(cnf_transformation,[],[f37])).
% 1.68/0.59  fof(f37,plain,(
% 1.68/0.59    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.68/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f36])).
% 1.68/0.59  fof(f36,plain,(
% 1.68/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.68/0.59    introduced(choice_axiom,[])).
% 1.68/0.59  fof(f23,plain,(
% 1.68/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.68/0.59    inference(flattening,[],[f22])).
% 1.68/0.59  fof(f22,plain,(
% 1.68/0.59    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.68/0.59    inference(ennf_transformation,[],[f19])).
% 1.68/0.59  fof(f19,plain,(
% 1.68/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.68/0.59    inference(pure_predicate_removal,[],[f18])).
% 1.68/0.59  fof(f18,negated_conjecture,(
% 1.68/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.68/0.59    inference(negated_conjecture,[],[f17])).
% 1.68/0.59  fof(f17,conjecture,(
% 1.68/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.68/0.59  fof(f73,plain,(
% 1.68/0.59    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.68/0.59    inference(definition_unfolding,[],[f44,f72,f72])).
% 1.68/0.59  fof(f44,plain,(
% 1.68/0.59    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.68/0.59    inference(cnf_transformation,[],[f37])).
% 1.68/0.59  fof(f95,plain,(
% 1.68/0.59    v1_relat_1(sK3)),
% 1.68/0.59    inference(resolution,[],[f74,f58])).
% 1.68/0.59  fof(f58,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f30])).
% 1.68/0.59  fof(f30,plain,(
% 1.68/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.59    inference(ennf_transformation,[],[f14])).
% 1.68/0.59  fof(f14,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.68/0.59  fof(f391,plain,(
% 1.68/0.59    spl4_18),
% 1.68/0.59    inference(avatar_contradiction_clause,[],[f390])).
% 1.68/0.59  fof(f390,plain,(
% 1.68/0.59    $false | spl4_18),
% 1.68/0.59    inference(subsumption_resolution,[],[f41,f370])).
% 1.68/0.59  fof(f370,plain,(
% 1.68/0.59    ~v1_funct_1(sK3) | spl4_18),
% 1.68/0.59    inference(avatar_component_clause,[],[f369])).
% 1.68/0.59  fof(f369,plain,(
% 1.68/0.59    spl4_18 <=> v1_funct_1(sK3)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.68/0.59  fof(f41,plain,(
% 1.68/0.59    v1_funct_1(sK3)),
% 1.68/0.59    inference(cnf_transformation,[],[f37])).
% 1.68/0.59  fof(f374,plain,(
% 1.68/0.59    ~spl4_3 | ~spl4_18 | spl4_19 | ~spl4_2),
% 1.68/0.59    inference(avatar_split_clause,[],[f367,f107,f372,f369,f149])).
% 1.68/0.59  fof(f149,plain,(
% 1.68/0.59    spl4_3 <=> v1_relat_1(sK3)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.68/0.59  fof(f107,plain,(
% 1.68/0.59    spl4_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.68/0.59  fof(f367,plain,(
% 1.68/0.59    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.68/0.59    inference(equality_resolution,[],[f286])).
% 1.68/0.59  fof(f286,plain,(
% 1.68/0.59    ( ! [X6] : (k1_relat_1(sK3) != k1_relat_1(X6) | k2_relat_1(X6) = k2_enumset1(k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0),k1_funct_1(X6,sK0)) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) ) | ~spl4_2),
% 1.68/0.59    inference(superposition,[],[f75,f108])).
% 1.68/0.59  fof(f108,plain,(
% 1.68/0.59    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_2),
% 1.68/0.59    inference(avatar_component_clause,[],[f107])).
% 1.68/0.60  fof(f75,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f56,f72,f72])).
% 1.68/0.60  fof(f56,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f29])).
% 1.68/0.60  fof(f29,plain,(
% 1.68/0.60    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.68/0.60    inference(flattening,[],[f28])).
% 1.68/0.60  fof(f28,plain,(
% 1.68/0.60    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.68/0.60    inference(ennf_transformation,[],[f13])).
% 1.68/0.60  fof(f13,axiom,(
% 1.68/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.68/0.60  fof(f261,plain,(
% 1.68/0.60    spl4_1 | spl4_2),
% 1.68/0.60    inference(avatar_split_clause,[],[f260,f107,f104])).
% 1.68/0.60  fof(f104,plain,(
% 1.68/0.60    spl4_1 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.68/0.60  fof(f260,plain,(
% 1.68/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.68/0.60    inference(duplicate_literal_removal,[],[f259])).
% 1.68/0.60  fof(f259,plain,(
% 1.68/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.68/0.60    inference(resolution,[],[f98,f84])).
% 1.68/0.60  fof(f84,plain,(
% 1.68/0.60    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k2_enumset1(X0,X0,X1,X2) = X3) )),
% 1.68/0.60    inference(definition_unfolding,[],[f62,f57,f71,f71,f71,f72,f72,f72,f57])).
% 1.68/0.60  fof(f62,plain,(
% 1.68/0.60    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f40])).
% 1.68/0.60  fof(f40,plain,(
% 1.68/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.68/0.60    inference(flattening,[],[f39])).
% 1.68/0.60  fof(f39,plain,(
% 1.68/0.60    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.68/0.60    inference(nnf_transformation,[],[f35])).
% 1.68/0.60  fof(f35,plain,(
% 1.68/0.60    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.68/0.60    inference(ennf_transformation,[],[f6])).
% 1.68/0.60  fof(f6,axiom,(
% 1.68/0.60    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.68/0.60  fof(f98,plain,(
% 1.68/0.60    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.68/0.60    inference(global_subsumption,[],[f95,f97])).
% 1.68/0.60  fof(f97,plain,(
% 1.68/0.60    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.68/0.60    inference(resolution,[],[f94,f54])).
% 1.68/0.60  fof(f54,plain,(
% 1.68/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f38])).
% 1.68/0.60  fof(f38,plain,(
% 1.68/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.68/0.60    inference(nnf_transformation,[],[f27])).
% 1.68/0.60  fof(f27,plain,(
% 1.68/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.68/0.60    inference(ennf_transformation,[],[f9])).
% 1.68/0.60  fof(f9,axiom,(
% 1.68/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.68/0.60  fof(f94,plain,(
% 1.68/0.60    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.68/0.60    inference(resolution,[],[f74,f59])).
% 1.68/0.60  fof(f59,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f31])).
% 1.68/0.60  fof(f31,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.60    inference(ennf_transformation,[],[f20])).
% 1.68/0.60  fof(f20,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.68/0.60    inference(pure_predicate_removal,[],[f15])).
% 1.68/0.60  fof(f15,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.68/0.60  fof(f227,plain,(
% 1.68/0.60    ~spl4_7),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f225])).
% 1.68/0.60  fof(f225,plain,(
% 1.68/0.60    $false | ~spl4_7),
% 1.68/0.60    inference(resolution,[],[f220,f47])).
% 1.68/0.60  fof(f47,plain,(
% 1.68/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f2])).
% 1.68/0.60  fof(f2,axiom,(
% 1.68/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.68/0.60  fof(f220,plain,(
% 1.68/0.60    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_7),
% 1.68/0.60    inference(forward_demodulation,[],[f216,f46])).
% 1.68/0.60  fof(f46,plain,(
% 1.68/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.68/0.60    inference(cnf_transformation,[],[f11])).
% 1.68/0.60  fof(f11,axiom,(
% 1.68/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.68/0.60  fof(f216,plain,(
% 1.68/0.60    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | ~spl4_7),
% 1.68/0.60    inference(backward_demodulation,[],[f170,f198])).
% 1.68/0.60  fof(f198,plain,(
% 1.68/0.60    k1_xboole_0 = sK3 | ~spl4_7),
% 1.68/0.60    inference(avatar_component_clause,[],[f197])).
% 1.68/0.60  fof(f197,plain,(
% 1.68/0.60    spl4_7 <=> k1_xboole_0 = sK3),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.68/0.60  fof(f170,plain,(
% 1.68/0.60    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 1.68/0.60    inference(global_subsumption,[],[f95,f168])).
% 1.68/0.60  fof(f168,plain,(
% 1.68/0.60    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3)),
% 1.68/0.60    inference(resolution,[],[f121,f53])).
% 1.68/0.60  fof(f121,plain,(
% 1.68/0.60    ( ! [X0] : (~r1_tarski(k9_relat_1(sK3,sK2),X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.68/0.60    inference(resolution,[],[f112,f60])).
% 1.68/0.60  fof(f60,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f33])).
% 1.68/0.60  fof(f33,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.68/0.60    inference(flattening,[],[f32])).
% 1.68/0.60  fof(f32,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.68/0.60    inference(ennf_transformation,[],[f1])).
% 1.68/0.60  fof(f1,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.68/0.60  fof(f112,plain,(
% 1.68/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k1_xboole_0)),
% 1.68/0.60    inference(resolution,[],[f110,f92])).
% 1.68/0.60  fof(f92,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.68/0.60    inference(equality_resolution,[],[f83])).
% 1.68/0.60  fof(f83,plain,(
% 1.68/0.60    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k1_xboole_0 != X3) )),
% 1.68/0.60    inference(definition_unfolding,[],[f63,f57])).
% 1.68/0.60  fof(f63,plain,(
% 1.68/0.60    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_xboole_0 != X3) )),
% 1.68/0.60    inference(cnf_transformation,[],[f40])).
% 1.68/0.60  fof(f110,plain,(
% 1.68/0.60    ( ! [X0] : (~r1_tarski(X0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | ~r1_tarski(k9_relat_1(sK3,sK2),X0)) )),
% 1.68/0.60    inference(resolution,[],[f99,f60])).
% 1.68/0.60  fof(f199,plain,(
% 1.68/0.60    ~spl4_3 | spl4_7 | ~spl4_1),
% 1.68/0.60    inference(avatar_split_clause,[],[f191,f104,f197,f149])).
% 1.68/0.60  fof(f191,plain,(
% 1.68/0.60    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_1),
% 1.68/0.60    inference(trivial_inequality_removal,[],[f190])).
% 1.68/0.60  fof(f190,plain,(
% 1.68/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_1),
% 1.68/0.60    inference(superposition,[],[f50,f105])).
% 1.68/0.60  % (21233)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.68/0.60  fof(f105,plain,(
% 1.68/0.60    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_1),
% 1.68/0.60    inference(avatar_component_clause,[],[f104])).
% 1.68/0.60  fof(f50,plain,(
% 1.68/0.60    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f25,plain,(
% 1.68/0.60    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.68/0.60    inference(flattening,[],[f24])).
% 1.68/0.60  fof(f24,plain,(
% 1.68/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.68/0.60    inference(ennf_transformation,[],[f12])).
% 1.68/0.60  fof(f12,axiom,(
% 1.68/0.60    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.68/0.60  fof(f156,plain,(
% 1.68/0.60    spl4_3),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f155])).
% 1.68/0.60  fof(f155,plain,(
% 1.68/0.60    $false | spl4_3),
% 1.68/0.60    inference(subsumption_resolution,[],[f95,f150])).
% 1.68/0.60  fof(f150,plain,(
% 1.68/0.60    ~v1_relat_1(sK3) | spl4_3),
% 1.68/0.60    inference(avatar_component_clause,[],[f149])).
% 1.68/0.60  % SZS output end Proof for theBenchmark
% 1.68/0.60  % (21219)------------------------------
% 1.68/0.60  % (21219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (21219)Termination reason: Refutation
% 1.68/0.60  
% 1.68/0.60  % (21219)Memory used [KB]: 10874
% 1.68/0.60  % (21219)Time elapsed: 0.155 s
% 1.68/0.60  % (21219)------------------------------
% 1.68/0.60  % (21219)------------------------------
% 1.68/0.60  % (21216)Success in time 0.233 s
%------------------------------------------------------------------------------
