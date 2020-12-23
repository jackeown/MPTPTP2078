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
% DateTime   : Thu Dec  3 13:04:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 606 expanded)
%              Number of leaves         :   19 ( 171 expanded)
%              Depth                    :   22
%              Number of atoms          :  276 (1426 expanded)
%              Number of equality atoms :  113 ( 553 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f114,f187,f190,f193])).

fof(f193,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f191,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f35])).

fof(f35,plain,
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

fof(f191,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f77,f186])).

fof(f186,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_8
  <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f77,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f65,f73])).

fof(f73,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f66,f62])).

fof(f62,plain,(
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

fof(f65,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f43,f64,f64])).

fof(f43,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f190,plain,
    ( ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f182,f88])).

fof(f88,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f182,plain,
    ( ! [X0] : k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_7
  <=> ! [X0] : k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f187,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f179,f90,f86,f184,f181])).

fof(f90,plain,
    ( spl4_2
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f179,plain,
    ( ! [X0] :
        ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) )
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f178,f91])).

fof(f91,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f178,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK3)
        | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f177,f122])).

fof(f122,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f82,f88])).

fof(f82,plain,(
    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f81,f75])).

fof(f81,plain,
    ( sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f74,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f66,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f177,plain,
    ( ! [X0] :
        ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f176,f75])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f175,f122])).

fof(f175,plain,
    ( ! [X0] :
        ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | ~ v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f174,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | ~ v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f173,f122])).

fof(f173,plain,
    ( ! [X0] :
        ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
        | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | ~ v1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)))
        | ~ v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f172,f122])).

fof(f172,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k2_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k2_enumset1(k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0),k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0),k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0),k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0))
        | ~ v1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)))
        | ~ v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) )
    | ~ spl4_1 ),
    inference(inner_rewriting,[],[f163])).

fof(f163,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0))
        | ~ v1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)))
        | ~ v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) )
    | ~ spl4_1 ),
    inference(superposition,[],[f133,f88])).

fof(f133,plain,(
    ! [X2,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X2,X2,X2,X2)
      | k2_relat_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2))
      | ~ v1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)))
      | ~ v1_relat_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)))
      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(superposition,[],[f67,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)))
      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) ) ),
    inference(resolution,[],[f78,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f54,f64,f64])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f64,f64])).

fof(f52,plain,(
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

fof(f114,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f112,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f105,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f105,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f77,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f97,f75])).

fof(f97,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(superposition,[],[f47,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f93,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f84,f90,f86])).

fof(f84,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f83,f70])).

fof(f83,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f78,f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (30466)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (30470)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.47  % (30476)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.47  % (30484)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.48  % (30462)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (30470)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f93,f114,f187,f190,f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~spl4_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    $false | ~spl4_8),
% 0.21/0.49    inference(subsumption_resolution,[],[f191,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f75,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f66,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f46,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f49,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.49  fof(f18,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f17])).
% 0.21/0.49  fof(f17,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_8),
% 0.21/0.49    inference(backward_demodulation,[],[f77,f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl4_8 <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f65,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.21/0.49    inference(resolution,[],[f66,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.21/0.49    inference(definition_unfolding,[],[f43,f64,f64])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    $false | (~spl4_1 | ~spl4_7)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f188])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    k1_relat_1(sK3) != k1_relat_1(sK3) | (~spl4_1 | ~spl4_7)),
% 0.21/0.49    inference(superposition,[],[f182,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl4_1 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)) ) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f181])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl4_7 <=> ! [X0] : k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl4_7 | spl4_8 | ~spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f179,f90,f86,f184,f181])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl4_2 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)) ) | (~spl4_1 | spl4_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f178,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(sK3) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)) ) | ~spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f177,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) | ~spl4_1),
% 0.21/0.49    inference(backward_demodulation,[],[f82,f88])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f75])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    sK3 = k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f74,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.49    inference(resolution,[],[f66,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f75])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f175,f122])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | ~v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f174,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | ~v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f173,f122])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | ~v1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3))) | ~v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f172,f122])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k2_enumset1(k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0),k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0),k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0),k1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK0)) | ~v1_funct_1(k7_relat_1(sK3,k1_relat_1(sK3))) | ~v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ) | ~spl4_1),
% 0.21/0.49    inference(inner_rewriting,[],[f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),sK0)) | ~v1_funct_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) | ~v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)))) ) | ~spl4_1),
% 0.21/0.49    inference(superposition,[],[f133,f88])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X2,X2,X2,X2) | k2_relat_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2),k1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)),X2)) | ~v1_funct_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1))) | ~v1_relat_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X1,X1,X1,X1)))) )),
% 0.21/0.49    inference(superposition,[],[f67,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.21/0.49    inference(resolution,[],[f78,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f54,f64,f64])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) )),
% 0.21/0.49    inference(resolution,[],[f75,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f52,f64,f64])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~spl4_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    $false | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f55,f64])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.49    inference(forward_demodulation,[],[f105,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.49    inference(backward_demodulation,[],[f77,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f75])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_2),
% 0.21/0.49    inference(superposition,[],[f47,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f84,f90,f86])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f83,f70])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.49    inference(superposition,[],[f78,f82])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30470)------------------------------
% 0.21/0.49  % (30470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30470)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30470)Memory used [KB]: 10746
% 0.21/0.49  % (30470)Time elapsed: 0.095 s
% 0.21/0.49  % (30470)------------------------------
% 0.21/0.49  % (30470)------------------------------
% 0.21/0.49  % (30484)Refutation not found, incomplete strategy% (30484)------------------------------
% 0.21/0.49  % (30484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30484)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30484)Memory used [KB]: 10746
% 0.21/0.49  % (30484)Time elapsed: 0.083 s
% 0.21/0.49  % (30484)------------------------------
% 0.21/0.49  % (30484)------------------------------
% 0.21/0.49  % (30461)Success in time 0.126 s
%------------------------------------------------------------------------------
