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
% DateTime   : Thu Dec  3 13:04:01 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 148 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  261 ( 456 expanded)
%              Number of equality atoms :   61 ( 106 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f104,f108,f121,f132,f140,f151,f164])).

fof(f164,plain,
    ( spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f131,f157])).

fof(f157,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f123,f150])).

fof(f150,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_12
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f123,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f131,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f151,plain,
    ( ~ spl3_5
    | spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f141,f137,f148,f91])).

fof(f91,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f137,plain,
    ( spl3_11
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f141,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f139,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f139,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( spl3_11
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f135,f91,f86,f76,f137])).

fof(f76,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f135,plain,
    ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f39,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f132,plain,
    ( ~ spl3_7
    | ~ spl3_9
    | ~ spl3_1
    | ~ spl3_10
    | spl3_3 ),
    inference(avatar_split_clause,[],[f127,f81,f129,f71,f118,f101])).

fof(f101,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f118,plain,
    ( spl3_9
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f71,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,
    ( spl3_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f127,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(resolution,[],[f38,f83])).

fof(f83,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f121,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f116,f91,f118])).

fof(f116,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f54,f93])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f108,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f47,f99])).

fof(f99,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_6
  <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f104,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f95,f91,f101,f97])).

fof(f95,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl3_5 ),
    inference(resolution,[],[f46,f93])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f94,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f58,f91])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f89,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f59,f86])).

fof(f59,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f31,f57])).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f81])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n007.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 12:18:21 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.44  % (26031)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.17/0.45  % (26039)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.17/0.47  % (26039)Refutation found. Thanks to Tanya!
% 0.17/0.47  % SZS status Theorem for theBenchmark
% 0.17/0.47  % SZS output start Proof for theBenchmark
% 0.17/0.47  fof(f165,plain,(
% 0.17/0.47    $false),
% 0.17/0.47    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f104,f108,f121,f132,f140,f151,f164])).
% 0.17/0.47  fof(f164,plain,(
% 0.17/0.47    spl3_10 | ~spl3_12),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f162])).
% 0.17/0.47  fof(f162,plain,(
% 0.17/0.47    $false | (spl3_10 | ~spl3_12)),
% 0.17/0.47    inference(subsumption_resolution,[],[f131,f157])).
% 0.17/0.47  fof(f157,plain,(
% 0.17/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_12),
% 0.17/0.47    inference(superposition,[],[f123,f150])).
% 0.17/0.47  fof(f150,plain,(
% 0.17/0.47    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl3_12),
% 0.17/0.47    inference(avatar_component_clause,[],[f148])).
% 0.17/0.47  fof(f148,plain,(
% 0.17/0.47    spl3_12 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.17/0.47  fof(f123,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.17/0.47    inference(resolution,[],[f62,f68])).
% 0.17/0.47  fof(f68,plain,(
% 0.17/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.47    inference(equality_resolution,[],[f50])).
% 0.17/0.47  fof(f50,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.47    inference(cnf_transformation,[],[f29])).
% 0.17/0.47  fof(f29,plain,(
% 0.17/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.47    inference(flattening,[],[f28])).
% 0.17/0.47  fof(f28,plain,(
% 0.17/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.47    inference(nnf_transformation,[],[f1])).
% 0.17/0.47  fof(f1,axiom,(
% 0.17/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.47  fof(f62,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.17/0.47    inference(definition_unfolding,[],[f35,f56])).
% 0.17/0.47  fof(f56,plain,(
% 0.17/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.17/0.47    inference(definition_unfolding,[],[f52,f55])).
% 0.17/0.47  fof(f55,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f4])).
% 0.17/0.47  fof(f4,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.17/0.47  fof(f52,plain,(
% 0.17/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f3])).
% 0.17/0.47  fof(f3,axiom,(
% 0.17/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.17/0.47  fof(f35,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f26])).
% 0.17/0.47  fof(f26,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.17/0.47    inference(flattening,[],[f25])).
% 0.17/0.47  fof(f25,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.17/0.47    inference(nnf_transformation,[],[f5])).
% 0.17/0.47  fof(f5,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.17/0.47  fof(f131,plain,(
% 0.17/0.47    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl3_10),
% 0.17/0.47    inference(avatar_component_clause,[],[f129])).
% 0.17/0.47  fof(f129,plain,(
% 0.17/0.47    spl3_10 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.17/0.47  fof(f151,plain,(
% 0.17/0.47    ~spl3_5 | spl3_12 | ~spl3_11),
% 0.17/0.47    inference(avatar_split_clause,[],[f141,f137,f148,f91])).
% 0.17/0.47  fof(f91,plain,(
% 0.17/0.47    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.17/0.47  fof(f137,plain,(
% 0.17/0.47    spl3_11 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.17/0.47  fof(f141,plain,(
% 0.17/0.47    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_11),
% 0.17/0.47    inference(superposition,[],[f139,f45])).
% 0.17/0.47  fof(f45,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.47    inference(cnf_transformation,[],[f20])).
% 0.17/0.47  fof(f20,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f10])).
% 0.17/0.47  fof(f10,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.17/0.47  fof(f139,plain,(
% 0.17/0.47    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~spl3_11),
% 0.17/0.47    inference(avatar_component_clause,[],[f137])).
% 0.17/0.47  fof(f140,plain,(
% 0.17/0.47    spl3_11 | spl3_2 | ~spl3_4 | ~spl3_5),
% 0.17/0.47    inference(avatar_split_clause,[],[f135,f91,f86,f76,f137])).
% 0.17/0.47  fof(f76,plain,(
% 0.17/0.47    spl3_2 <=> k1_xboole_0 = sK1),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.47  fof(f86,plain,(
% 0.17/0.47    spl3_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.17/0.47  fof(f135,plain,(
% 0.17/0.47    ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~spl3_5),
% 0.17/0.47    inference(resolution,[],[f39,f93])).
% 0.17/0.47  fof(f93,plain,(
% 0.17/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_5),
% 0.17/0.47    inference(avatar_component_clause,[],[f91])).
% 0.17/0.47  fof(f39,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.17/0.47    inference(cnf_transformation,[],[f27])).
% 0.17/0.47  fof(f27,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(nnf_transformation,[],[f19])).
% 0.17/0.47  fof(f19,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(flattening,[],[f18])).
% 0.17/0.47  fof(f18,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f11])).
% 0.17/0.47  fof(f11,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.17/0.47  fof(f132,plain,(
% 0.17/0.47    ~spl3_7 | ~spl3_9 | ~spl3_1 | ~spl3_10 | spl3_3),
% 0.17/0.47    inference(avatar_split_clause,[],[f127,f81,f129,f71,f118,f101])).
% 0.17/0.47  fof(f101,plain,(
% 0.17/0.47    spl3_7 <=> v1_relat_1(sK2)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.17/0.47  fof(f118,plain,(
% 0.17/0.47    spl3_9 <=> v5_relat_1(sK2,sK1)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.17/0.47  fof(f71,plain,(
% 0.17/0.47    spl3_1 <=> v1_funct_1(sK2)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.47  fof(f81,plain,(
% 0.17/0.47    spl3_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.47  fof(f127,plain,(
% 0.17/0.47    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl3_3),
% 0.17/0.47    inference(resolution,[],[f38,f83])).
% 0.17/0.47  fof(f83,plain,(
% 0.17/0.47    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl3_3),
% 0.17/0.47    inference(avatar_component_clause,[],[f81])).
% 0.17/0.47  fof(f38,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f17])).
% 0.17/0.47  fof(f17,plain,(
% 0.17/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.17/0.47    inference(flattening,[],[f16])).
% 0.17/0.47  fof(f16,plain,(
% 0.17/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.17/0.47    inference(ennf_transformation,[],[f8])).
% 0.17/0.47  fof(f8,axiom,(
% 0.17/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.17/0.47  fof(f121,plain,(
% 0.17/0.47    spl3_9 | ~spl3_5),
% 0.17/0.47    inference(avatar_split_clause,[],[f116,f91,f118])).
% 0.17/0.47  fof(f116,plain,(
% 0.17/0.47    v5_relat_1(sK2,sK1) | ~spl3_5),
% 0.17/0.47    inference(resolution,[],[f54,f93])).
% 0.17/0.47  fof(f54,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f22])).
% 0.17/0.47  fof(f22,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f9])).
% 0.17/0.47  fof(f9,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.17/0.47  fof(f108,plain,(
% 0.17/0.47    spl3_6),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f105])).
% 0.17/0.47  fof(f105,plain,(
% 0.17/0.47    $false | spl3_6),
% 0.17/0.47    inference(unit_resulting_resolution,[],[f47,f99])).
% 0.17/0.47  fof(f99,plain,(
% 0.17/0.47    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl3_6),
% 0.17/0.47    inference(avatar_component_clause,[],[f97])).
% 0.17/0.47  fof(f97,plain,(
% 0.17/0.47    spl3_6 <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.17/0.47  fof(f47,plain,(
% 0.17/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.17/0.47    inference(cnf_transformation,[],[f7])).
% 0.17/0.47  fof(f7,axiom,(
% 0.17/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.17/0.47  fof(f104,plain,(
% 0.17/0.47    ~spl3_6 | spl3_7 | ~spl3_5),
% 0.17/0.47    inference(avatar_split_clause,[],[f95,f91,f101,f97])).
% 0.17/0.47  fof(f95,plain,(
% 0.17/0.47    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl3_5),
% 0.17/0.47    inference(resolution,[],[f46,f93])).
% 0.17/0.47  fof(f46,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f21])).
% 0.17/0.47  fof(f21,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.17/0.47    inference(ennf_transformation,[],[f6])).
% 0.17/0.47  fof(f6,axiom,(
% 0.17/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.17/0.47  fof(f94,plain,(
% 0.17/0.47    spl3_5),
% 0.17/0.47    inference(avatar_split_clause,[],[f58,f91])).
% 0.17/0.47  fof(f58,plain,(
% 0.17/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.17/0.47    inference(definition_unfolding,[],[f32,f57])).
% 0.17/0.47  fof(f57,plain,(
% 0.17/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.17/0.47    inference(definition_unfolding,[],[f48,f56])).
% 0.17/0.47  fof(f48,plain,(
% 0.17/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f2])).
% 0.17/0.47  fof(f2,axiom,(
% 0.17/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.47  fof(f32,plain,(
% 0.17/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f24,plain,(
% 0.17/0.47    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.17/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).
% 0.17/0.47  fof(f23,plain,(
% 0.17/0.47    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.17/0.47    introduced(choice_axiom,[])).
% 0.17/0.47  fof(f15,plain,(
% 0.17/0.47    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.17/0.47    inference(flattening,[],[f14])).
% 0.17/0.47  fof(f14,plain,(
% 0.17/0.47    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.17/0.47    inference(ennf_transformation,[],[f13])).
% 0.17/0.47  fof(f13,negated_conjecture,(
% 0.17/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.17/0.47    inference(negated_conjecture,[],[f12])).
% 0.17/0.47  fof(f12,conjecture,(
% 0.17/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.17/0.47  fof(f89,plain,(
% 0.17/0.47    spl3_4),
% 0.17/0.47    inference(avatar_split_clause,[],[f59,f86])).
% 0.17/0.47  fof(f59,plain,(
% 0.17/0.47    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.17/0.47    inference(definition_unfolding,[],[f31,f57])).
% 0.17/0.47  fof(f31,plain,(
% 0.17/0.47    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f84,plain,(
% 0.17/0.47    ~spl3_3),
% 0.17/0.47    inference(avatar_split_clause,[],[f34,f81])).
% 0.17/0.47  fof(f34,plain,(
% 0.17/0.47    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f79,plain,(
% 0.17/0.47    ~spl3_2),
% 0.17/0.47    inference(avatar_split_clause,[],[f33,f76])).
% 0.17/0.47  fof(f33,plain,(
% 0.17/0.47    k1_xboole_0 != sK1),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f74,plain,(
% 0.17/0.47    spl3_1),
% 0.17/0.47    inference(avatar_split_clause,[],[f30,f71])).
% 0.17/0.47  fof(f30,plain,(
% 0.17/0.47    v1_funct_1(sK2)),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  % SZS output end Proof for theBenchmark
% 0.17/0.47  % (26039)------------------------------
% 0.17/0.47  % (26039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.47  % (26039)Termination reason: Refutation
% 0.17/0.47  
% 0.17/0.47  % (26039)Memory used [KB]: 10746
% 0.17/0.47  % (26039)Time elapsed: 0.098 s
% 0.17/0.47  % (26039)------------------------------
% 0.17/0.47  % (26039)------------------------------
% 0.17/0.47  % (26014)Success in time 0.147 s
%------------------------------------------------------------------------------
