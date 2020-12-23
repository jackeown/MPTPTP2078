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
% DateTime   : Thu Dec  3 13:04:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 159 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  277 ( 499 expanded)
%              Number of equality atoms :  101 ( 181 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f100,f148,f149,f152,f159,f167,f174,f175])).

fof(f175,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f174,plain,
    ( ~ spl6_16
    | ~ spl6_5
    | ~ spl6_6
    | spl6_15 ),
    inference(avatar_split_clause,[],[f168,f164,f85,f79,f171])).

fof(f171,plain,
    ( spl6_16
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f79,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f85,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f164,plain,
    ( spl6_15
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f168,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f86,f81,f166,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f37,f34,f34])).

fof(f34,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f166,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f81,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f86,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f167,plain,
    ( ~ spl6_15
    | spl6_1
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f162,f139,f59,f164])).

fof(f59,plain,
    ( spl6_1
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f139,plain,
    ( spl6_13
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f162,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl6_1
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f61,f141])).

fof(f141,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f61,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f159,plain,
    ( ~ spl6_3
    | spl6_6
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl6_3
    | spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f153,f99])).

fof(f99,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_8
  <=> r2_hidden(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f153,plain,
    ( ~ r2_hidden(sK3(sK2),sK2)
    | ~ spl6_3
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f71,f93,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK5(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK5(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f93,plain,
    ( ! [X0,X1] : k4_tarski(X0,X1) != sK3(sK2)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f87,f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( v1_relat_1(X0)
      | k4_tarski(X2,X3) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f24])).

% (31521)Termination reason: Refutation not found, incomplete strategy

% (31521)Memory used [KB]: 10618
fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

% (31521)Time elapsed: 0.066 s
% (31521)------------------------------
% (31521)------------------------------
fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f152,plain,
    ( spl6_12
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f151,f74,f69,f64,f134])).

fof(f134,plain,
    ( spl6_12
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f64,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f74,plain,
    ( spl6_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f151,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f150,f66])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f150,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f113,f76])).

fof(f76,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f113,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f149,plain,
    ( spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f112,f69,f139])).

fof(f112,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f148,plain,
    ( spl6_14
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f111,f69,f144])).

fof(f144,plain,
    ( spl6_14
  <=> k1_relat_1(sK2) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f111,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f100,plain,
    ( spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f92,f85,f97])).

fof(f92,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f87,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).

fof(f22,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f74])).

fof(f51,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f50,f69])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f59])).

fof(f49,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f33,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (31529)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.48  % (31529)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % (31521)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.49  % (31521)Refutation not found, incomplete strategy% (31521)------------------------------
% 0.23/0.49  % (31521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f176,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f100,f148,f149,f152,f159,f167,f174,f175])).
% 0.23/0.49  fof(f175,plain,(
% 0.23/0.49    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.23/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.49  fof(f174,plain,(
% 0.23/0.49    ~spl6_16 | ~spl6_5 | ~spl6_6 | spl6_15),
% 0.23/0.49    inference(avatar_split_clause,[],[f168,f164,f85,f79,f171])).
% 0.23/0.49  fof(f171,plain,(
% 0.23/0.49    spl6_16 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.23/0.49  fof(f79,plain,(
% 0.23/0.49    spl6_5 <=> v1_funct_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.23/0.49  fof(f85,plain,(
% 0.23/0.49    spl6_6 <=> v1_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.23/0.49  fof(f164,plain,(
% 0.23/0.49    spl6_15 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.23/0.49  fof(f168,plain,(
% 0.23/0.49    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2) | (~spl6_5 | ~spl6_6 | spl6_15)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f86,f81,f166,f52])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f37,f34,f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(flattening,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.49    inference(ennf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.23/0.49  fof(f166,plain,(
% 0.23/0.49    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | spl6_15),
% 0.23/0.49    inference(avatar_component_clause,[],[f164])).
% 0.23/0.49  fof(f81,plain,(
% 0.23/0.49    v1_funct_1(sK2) | ~spl6_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f79])).
% 0.23/0.49  fof(f86,plain,(
% 0.23/0.49    v1_relat_1(sK2) | ~spl6_6),
% 0.23/0.49    inference(avatar_component_clause,[],[f85])).
% 0.23/0.49  fof(f167,plain,(
% 0.23/0.49    ~spl6_15 | spl6_1 | ~spl6_13),
% 0.23/0.49    inference(avatar_split_clause,[],[f162,f139,f59,f164])).
% 0.23/0.49  fof(f59,plain,(
% 0.23/0.49    spl6_1 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.49  fof(f139,plain,(
% 0.23/0.49    spl6_13 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.23/0.49  fof(f162,plain,(
% 0.23/0.49    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | (spl6_1 | ~spl6_13)),
% 0.23/0.49    inference(backward_demodulation,[],[f61,f141])).
% 0.23/0.49  fof(f141,plain,(
% 0.23/0.49    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl6_13),
% 0.23/0.49    inference(avatar_component_clause,[],[f139])).
% 0.23/0.49  fof(f61,plain,(
% 0.23/0.49    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl6_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f59])).
% 0.23/0.49  fof(f159,plain,(
% 0.23/0.49    ~spl6_3 | spl6_6 | ~spl6_8),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f158])).
% 0.23/0.49  fof(f158,plain,(
% 0.23/0.49    $false | (~spl6_3 | spl6_6 | ~spl6_8)),
% 0.23/0.49    inference(subsumption_resolution,[],[f153,f99])).
% 0.23/0.49  fof(f99,plain,(
% 0.23/0.49    r2_hidden(sK3(sK2),sK2) | ~spl6_8),
% 0.23/0.49    inference(avatar_component_clause,[],[f97])).
% 0.23/0.49  fof(f97,plain,(
% 0.23/0.49    spl6_8 <=> r2_hidden(sK3(sK2),sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.23/0.49  fof(f153,plain,(
% 0.23/0.49    ~r2_hidden(sK3(sK2),sK2) | (~spl6_3 | spl6_6)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f71,f93,f46])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0 | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(sK5(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK5(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.49    inference(flattening,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.23/0.49  fof(f93,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK3(sK2)) ) | spl6_6),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f87,f36])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X2,X0,X3] : (v1_relat_1(X0) | k4_tarski(X2,X3) != sK3(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f24])).
% 0.23/0.49  % (31521)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (31521)Memory used [KB]: 10618
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  % (31521)Time elapsed: 0.066 s
% 0.23/0.49  % (31521)------------------------------
% 0.23/0.49  % (31521)------------------------------
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.23/0.49    inference(unused_predicate_definition_removal,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.23/0.49  fof(f87,plain,(
% 0.23/0.49    ~v1_relat_1(sK2) | spl6_6),
% 0.23/0.49    inference(avatar_component_clause,[],[f85])).
% 0.23/0.49  fof(f71,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl6_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f69])).
% 0.23/0.49  fof(f69,plain,(
% 0.23/0.49    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.23/0.49  fof(f152,plain,(
% 0.23/0.49    spl6_12 | spl6_2 | ~spl6_3 | ~spl6_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f151,f74,f69,f64,f134])).
% 0.23/0.49  fof(f134,plain,(
% 0.23/0.49    spl6_12 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.23/0.49  fof(f64,plain,(
% 0.23/0.49    spl6_2 <=> k1_xboole_0 = sK1),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.49  fof(f74,plain,(
% 0.23/0.49    spl6_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.23/0.49  fof(f151,plain,(
% 0.23/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.23/0.49    inference(subsumption_resolution,[],[f150,f66])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    k1_xboole_0 != sK1 | spl6_2),
% 0.23/0.49    inference(avatar_component_clause,[],[f64])).
% 0.23/0.49  fof(f150,plain,(
% 0.23/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | k1_xboole_0 = sK1 | (~spl6_3 | ~spl6_4)),
% 0.23/0.49    inference(subsumption_resolution,[],[f113,f76])).
% 0.23/0.49  fof(f76,plain,(
% 0.23/0.49    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl6_4),
% 0.23/0.49    inference(avatar_component_clause,[],[f74])).
% 0.23/0.49  fof(f113,plain,(
% 0.23/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | ~spl6_3),
% 0.23/0.49    inference(resolution,[],[f71,f40])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(nnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(flattening,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(ennf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.23/0.49  fof(f149,plain,(
% 0.23/0.49    spl6_13 | ~spl6_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f112,f69,f139])).
% 0.23/0.49  fof(f112,plain,(
% 0.23/0.49    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl6_3),
% 0.23/0.49    inference(resolution,[],[f71,f39])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(ennf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.49  fof(f148,plain,(
% 0.23/0.49    spl6_14 | ~spl6_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f111,f69,f144])).
% 0.23/0.49  fof(f144,plain,(
% 0.23/0.49    spl6_14 <=> k1_relat_1(sK2) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.23/0.49  fof(f111,plain,(
% 0.23/0.49    k1_relat_1(sK2) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~spl6_3),
% 0.23/0.49    inference(resolution,[],[f71,f38])).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    spl6_8 | spl6_6),
% 0.23/0.49    inference(avatar_split_clause,[],[f92,f85,f97])).
% 0.23/0.49  fof(f92,plain,(
% 0.23/0.49    r2_hidden(sK3(sK2),sK2) | spl6_6),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f87,f35])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f82,plain,(
% 0.23/0.49    spl6_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f29,f79])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    v1_funct_1(sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.23/0.49    inference(flattening,[],[f11])).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.23/0.49    inference(ennf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.23/0.49    inference(negated_conjecture,[],[f8])).
% 0.23/0.49  fof(f8,conjecture,(
% 0.23/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    spl6_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f51,f74])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.23/0.49    inference(definition_unfolding,[],[f30,f34])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f72,plain,(
% 0.23/0.49    spl6_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f50,f69])).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.49    inference(definition_unfolding,[],[f31,f34])).
% 0.23/0.49  fof(f31,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f67,plain,(
% 0.23/0.49    ~spl6_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f32,f64])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    k1_xboole_0 != sK1),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f62,plain,(
% 0.23/0.49    ~spl6_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f49,f59])).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.23/0.49    inference(definition_unfolding,[],[f33,f34,f34])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (31529)------------------------------
% 0.23/0.49  % (31529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (31529)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (31529)Memory used [KB]: 6268
% 0.23/0.49  % (31529)Time elapsed: 0.068 s
% 0.23/0.49  % (31529)------------------------------
% 0.23/0.49  % (31529)------------------------------
% 0.23/0.49  % (31503)Success in time 0.123 s
%------------------------------------------------------------------------------
