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
% DateTime   : Thu Dec  3 13:04:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 481 expanded)
%              Number of leaves         :   30 ( 157 expanded)
%              Depth                    :   14
%              Number of atoms          :  402 (1195 expanded)
%              Number of equality atoms :  143 ( 568 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f182,f203,f320,f322,f565,f566,f595,f606,f644,f708,f720])).

fof(f720,plain,(
    ~ spl5_31 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f137,f707])).

fof(f707,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f706])).

fof(f706,plain,
    ( spl5_31
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f137,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f92,f120])).

fof(f120,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f94,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f55,f91])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f44])).

fof(f44,plain,
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

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f92,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f57,f91,f91])).

fof(f57,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f708,plain,
    ( ~ spl5_7
    | ~ spl5_3
    | spl5_31
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f700,f134,f706,f159,f175])).

fof(f175,plain,
    ( spl5_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f159,plain,
    ( spl5_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f134,plain,
    ( spl5_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f700,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(equality_resolution,[],[f659])).

fof(f659,plain,
    ( ! [X2] :
        ( k1_relat_1(sK2) != k1_relat_1(X2)
        | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl5_2 ),
    inference(superposition,[],[f107,f135])).

fof(f135,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f91,f91])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f644,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f643,f134,f131])).

fof(f131,plain,
    ( spl5_1
  <=> o_0_0_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f643,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f642])).

fof(f642,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f126,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | o_0_0_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f84,f90,f91,f91,f58,f90])).

fof(f58,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f126,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(global_subsumption,[],[f121,f125])).

fof(f125,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f119,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f119,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f94,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f121,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f94,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f606,plain,
    ( ~ spl5_10
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f457,f310])).

fof(f310,plain,
    ( o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl5_15
  <=> o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f457,plain,
    ( o_0_0_xboole_0 != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f453,f96])).

fof(f96,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f60,f58,f58])).

fof(f60,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f453,plain,
    ( k2_relat_1(o_0_0_xboole_0) != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f137,f202])).

fof(f202,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_10
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f595,plain,
    ( ~ spl5_13
    | ~ spl5_14
    | spl5_15
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f594,f339,f309,f306,f303])).

fof(f303,plain,
    ( spl5_13
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f306,plain,
    ( spl5_14
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f339,plain,
    ( spl5_18
  <=> o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f594,plain,
    ( o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f593,f96])).

fof(f593,plain,
    ( k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl5_18 ),
    inference(trivial_inequality_removal,[],[f591])).

fof(f591,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl5_18 ),
    inference(superposition,[],[f575,f97])).

fof(f97,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f59,f58,f58])).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f575,plain,
    ( ! [X2] :
        ( o_0_0_xboole_0 != k1_relat_1(X2)
        | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl5_18 ),
    inference(superposition,[],[f107,f340])).

fof(f340,plain,
    ( o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f339])).

fof(f566,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f559,f201,f342,f339])).

fof(f342,plain,
    ( spl5_19
  <=> r2_hidden(k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f559,plain,
    ( r2_hidden(k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),o_0_0_xboole_0)
    | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f552,f104])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f58])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f552,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(o_0_0_xboole_0,X0),o_0_0_xboole_0) )
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f551,f96])).

fof(f551,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(o_0_0_xboole_0,X0),k2_relat_1(o_0_0_xboole_0))
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f369,f202])).

fof(f369,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f124,f120])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(global_subsumption,[],[f53,f93,f95,f118])).

fof(f118,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = sK1
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f94,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f89,f58])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f95,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f54,f91])).

fof(f54,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f565,plain,(
    ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl5_19 ),
    inference(resolution,[],[f558,f98])).

fof(f98,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f558,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl5_19 ),
    inference(resolution,[],[f343,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f343,plain,
    ( r2_hidden(k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),o_0_0_xboole_0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f342])).

fof(f322,plain,
    ( ~ spl5_10
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl5_10
    | spl5_14 ),
    inference(subsumption_resolution,[],[f232,f307])).

fof(f307,plain,
    ( ~ v1_funct_1(o_0_0_xboole_0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f306])).

fof(f232,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f53,f202])).

fof(f320,plain,
    ( ~ spl5_10
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f237,f304])).

fof(f304,plain,
    ( ~ v1_relat_1(o_0_0_xboole_0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f303])).

fof(f237,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f121,f202])).

fof(f203,plain,
    ( ~ spl5_7
    | spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f195,f131,f201,f175])).

fof(f195,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f101,f132])).

fof(f132,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f101,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 != k1_relat_1(X0)
      | o_0_0_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f58,f58])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f182,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f121,f176])).

fof(f176,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f175])).

fof(f172,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f53,f160])).

fof(f160,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (20120)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (20147)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (20131)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (20122)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (20137)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (20123)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (20141)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (20124)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20121)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20133)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (20124)Refutation not found, incomplete strategy% (20124)------------------------------
% 0.21/0.54  % (20124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20124)Memory used [KB]: 6268
% 0.21/0.54  % (20124)Time elapsed: 0.128 s
% 0.21/0.54  % (20124)------------------------------
% 0.21/0.54  % (20124)------------------------------
% 0.21/0.54  % (20131)Refutation not found, incomplete strategy% (20131)------------------------------
% 0.21/0.54  % (20131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20131)Memory used [KB]: 10618
% 0.21/0.54  % (20131)Time elapsed: 0.124 s
% 0.21/0.54  % (20131)------------------------------
% 0.21/0.54  % (20131)------------------------------
% 0.21/0.54  % (20148)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (20126)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (20127)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (20130)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20122)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (20128)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (20150)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (20142)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (20129)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (20136)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (20144)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (20132)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (20140)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (20135)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (20132)Refutation not found, incomplete strategy% (20132)------------------------------
% 0.21/0.55  % (20132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20132)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20132)Memory used [KB]: 10746
% 0.21/0.55  % (20132)Time elapsed: 0.145 s
% 0.21/0.55  % (20132)------------------------------
% 0.21/0.55  % (20132)------------------------------
% 0.21/0.56  % (20149)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (20143)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (20139)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (20141)Refutation not found, incomplete strategy% (20141)------------------------------
% 0.21/0.56  % (20141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20141)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20141)Memory used [KB]: 10874
% 0.21/0.56  % (20141)Time elapsed: 0.131 s
% 0.21/0.56  % (20141)------------------------------
% 0.21/0.56  % (20141)------------------------------
% 0.21/0.56  % (20146)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (20143)Refutation not found, incomplete strategy% (20143)------------------------------
% 0.21/0.56  % (20143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20143)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20143)Memory used [KB]: 10746
% 0.21/0.56  % (20143)Time elapsed: 0.144 s
% 0.21/0.56  % (20143)------------------------------
% 0.21/0.56  % (20143)------------------------------
% 0.21/0.56  % (20145)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (20134)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (20138)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (20138)Refutation not found, incomplete strategy% (20138)------------------------------
% 0.21/0.57  % (20138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20138)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20138)Memory used [KB]: 10618
% 0.21/0.57  % (20138)Time elapsed: 0.160 s
% 0.21/0.57  % (20138)------------------------------
% 0.21/0.57  % (20138)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f721,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f172,f182,f203,f320,f322,f565,f566,f595,f606,f644,f708,f720])).
% 0.21/0.57  fof(f720,plain,(
% 0.21/0.57    ~spl5_31),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f710])).
% 0.21/0.57  fof(f710,plain,(
% 0.21/0.57    $false | ~spl5_31),
% 0.21/0.57    inference(subsumption_resolution,[],[f137,f707])).
% 0.21/0.57  fof(f707,plain,(
% 0.21/0.57    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~spl5_31),
% 0.21/0.57    inference(avatar_component_clause,[],[f706])).
% 0.21/0.57  fof(f706,plain,(
% 0.21/0.57    spl5_31 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.21/0.57    inference(backward_demodulation,[],[f92,f120])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f94,f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.57    inference(definition_unfolding,[],[f55,f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f63,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f74,f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f21])).
% 0.21/0.57  fof(f21,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.57    inference(definition_unfolding,[],[f57,f91,f91])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f708,plain,(
% 0.21/0.57    ~spl5_7 | ~spl5_3 | spl5_31 | ~spl5_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f700,f134,f706,f159,f175])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    spl5_7 <=> v1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    spl5_3 <=> v1_funct_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    spl5_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.57  fof(f700,plain,(
% 0.21/0.57    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_2),
% 0.21/0.57    inference(equality_resolution,[],[f659])).
% 0.21/0.57  fof(f659,plain,(
% 0.21/0.57    ( ! [X2] : (k1_relat_1(sK2) != k1_relat_1(X2) | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl5_2),
% 0.21/0.57    inference(superposition,[],[f107,f135])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl5_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f134])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f77,f91,f91])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.57  fof(f644,plain,(
% 0.21/0.57    spl5_1 | spl5_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f643,f134,f131])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    spl5_1 <=> o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.57  fof(f643,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f642])).
% 0.21/0.57  fof(f642,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f126,f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X2) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f84,f90,f91,f91,f58,f90])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.57    inference(flattening,[],[f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.57    inference(nnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.57    inference(global_subsumption,[],[f121,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f119,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.57    inference(resolution,[],[f94,f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f94,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f606,plain,(
% 0.21/0.57    ~spl5_10 | ~spl5_15),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f596])).
% 0.21/0.57  fof(f596,plain,(
% 0.21/0.57    $false | (~spl5_10 | ~spl5_15)),
% 0.21/0.57    inference(subsumption_resolution,[],[f457,f310])).
% 0.21/0.57  fof(f310,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) | ~spl5_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f309])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    spl5_15 <=> o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.57  fof(f457,plain,(
% 0.21/0.57    o_0_0_xboole_0 != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) | ~spl5_10),
% 0.21/0.57    inference(forward_demodulation,[],[f453,f96])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.57    inference(definition_unfolding,[],[f60,f58,f58])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.57  fof(f453,plain,(
% 0.21/0.57    k2_relat_1(o_0_0_xboole_0) != k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) | ~spl5_10),
% 0.21/0.57    inference(backward_demodulation,[],[f137,f202])).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    o_0_0_xboole_0 = sK2 | ~spl5_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f201])).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    spl5_10 <=> o_0_0_xboole_0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.57  fof(f595,plain,(
% 0.21/0.57    ~spl5_13 | ~spl5_14 | spl5_15 | ~spl5_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f594,f339,f309,f306,f303])).
% 0.21/0.57  fof(f303,plain,(
% 0.21/0.57    spl5_13 <=> v1_relat_1(o_0_0_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.57  fof(f306,plain,(
% 0.21/0.57    spl5_14 <=> v1_funct_1(o_0_0_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.57  fof(f339,plain,(
% 0.21/0.57    spl5_18 <=> o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.57  fof(f594,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | ~spl5_18),
% 0.21/0.57    inference(forward_demodulation,[],[f593,f96])).
% 0.21/0.57  fof(f593,plain,(
% 0.21/0.57    k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | ~spl5_18),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f591])).
% 0.21/0.57  fof(f591,plain,(
% 0.21/0.57    o_0_0_xboole_0 != o_0_0_xboole_0 | k2_relat_1(o_0_0_xboole_0) = k2_enumset1(k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0),k1_funct_1(o_0_0_xboole_0,sK0)) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | ~spl5_18),
% 0.21/0.57    inference(superposition,[],[f575,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.21/0.57    inference(definition_unfolding,[],[f59,f58,f58])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f575,plain,(
% 0.21/0.57    ( ! [X2] : (o_0_0_xboole_0 != k1_relat_1(X2) | k2_relat_1(X2) = k2_enumset1(k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0),k1_funct_1(X2,sK0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl5_18),
% 0.21/0.57    inference(superposition,[],[f107,f340])).
% 0.21/0.57  fof(f340,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f339])).
% 0.21/0.57  fof(f566,plain,(
% 0.21/0.57    spl5_18 | spl5_19 | ~spl5_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f559,f201,f342,f339])).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    spl5_19 <=> r2_hidden(k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),o_0_0_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.57  fof(f559,plain,(
% 0.21/0.57    r2_hidden(k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),o_0_0_xboole_0) | o_0_0_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_10),
% 0.21/0.57    inference(resolution,[],[f552,f104])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f67,f58])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.57  fof(f552,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(o_0_0_xboole_0,X0),o_0_0_xboole_0)) ) | ~spl5_10),
% 0.21/0.57    inference(forward_demodulation,[],[f551,f96])).
% 0.21/0.57  fof(f551,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(o_0_0_xboole_0,X0),k2_relat_1(o_0_0_xboole_0)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl5_10),
% 0.21/0.57    inference(forward_demodulation,[],[f369,f202])).
% 0.21/0.57  fof(f369,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f124,f120])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 0.21/0.57    inference(global_subsumption,[],[f53,f93,f95,f118])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X0] : (o_0_0_xboole_0 = sK1 | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.57    inference(resolution,[],[f94,f113])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f89,f58])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.57    inference(flattening,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f91])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    o_0_0_xboole_0 != sK1),
% 0.21/0.57    inference(definition_unfolding,[],[f56,f58])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f565,plain,(
% 0.21/0.57    ~spl5_19),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f564])).
% 0.21/0.57  fof(f564,plain,(
% 0.21/0.57    $false | ~spl5_19),
% 0.21/0.57    inference(resolution,[],[f558,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f61,f58])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    ~r1_tarski(o_0_0_xboole_0,k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | ~spl5_19),
% 0.21/0.57    inference(resolution,[],[f343,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.57  fof(f343,plain,(
% 0.21/0.57    r2_hidden(k1_funct_1(o_0_0_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),o_0_0_xboole_0) | ~spl5_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f342])).
% 0.21/0.57  fof(f322,plain,(
% 0.21/0.57    ~spl5_10 | spl5_14),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f321])).
% 0.21/0.57  fof(f321,plain,(
% 0.21/0.57    $false | (~spl5_10 | spl5_14)),
% 0.21/0.57    inference(subsumption_resolution,[],[f232,f307])).
% 0.21/0.57  fof(f307,plain,(
% 0.21/0.57    ~v1_funct_1(o_0_0_xboole_0) | spl5_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f306])).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    v1_funct_1(o_0_0_xboole_0) | ~spl5_10),
% 0.21/0.57    inference(backward_demodulation,[],[f53,f202])).
% 0.21/0.57  fof(f320,plain,(
% 0.21/0.57    ~spl5_10 | spl5_13),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f319])).
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    $false | (~spl5_10 | spl5_13)),
% 0.21/0.57    inference(subsumption_resolution,[],[f237,f304])).
% 0.21/0.57  fof(f304,plain,(
% 0.21/0.57    ~v1_relat_1(o_0_0_xboole_0) | spl5_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f303])).
% 0.21/0.57  fof(f237,plain,(
% 0.21/0.57    v1_relat_1(o_0_0_xboole_0) | ~spl5_10),
% 0.21/0.57    inference(backward_demodulation,[],[f121,f202])).
% 0.21/0.57  fof(f203,plain,(
% 0.21/0.57    ~spl5_7 | spl5_10 | ~spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f195,f131,f201,f175])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    o_0_0_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f194])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    o_0_0_xboole_0 != o_0_0_xboole_0 | o_0_0_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.57    inference(superposition,[],[f101,f132])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k1_relat_1(sK2) | ~spl5_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f131])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ( ! [X0] : (o_0_0_xboole_0 != k1_relat_1(X0) | o_0_0_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f64,f58,f58])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    spl5_7),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    $false | spl5_7),
% 0.21/0.57    inference(subsumption_resolution,[],[f121,f176])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl5_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f175])).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    spl5_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    $false | spl5_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f53,f160])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | spl5_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f159])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20122)------------------------------
% 0.21/0.57  % (20122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20122)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20122)Memory used [KB]: 11001
% 0.21/0.57  % (20122)Time elapsed: 0.124 s
% 0.21/0.57  % (20122)------------------------------
% 0.21/0.57  % (20122)------------------------------
% 0.21/0.57  % (20116)Success in time 0.203 s
%------------------------------------------------------------------------------
