%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 191 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  274 ( 461 expanded)
%              Number of equality atoms :   69 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f107,f112,f116,f127,f132,f145,f155,f168,f192,f204,f213,f216])).

fof(f216,plain,
    ( ~ spl5_5
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl5_5
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f102,f212,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f212,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl5_20
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f102,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f213,plain,
    ( ~ spl5_14
    | ~ spl5_20
    | spl5_19 ),
    inference(avatar_split_clause,[],[f208,f201,f210,f165])).

fof(f165,plain,
    ( spl5_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f201,plain,
    ( spl5_19
  <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f208,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | spl5_19 ),
    inference(superposition,[],[f203,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f203,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( ~ spl5_19
    | spl5_9
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f199,f189,f142,f124,f201])).

fof(f124,plain,
    ( spl5_9
  <=> r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f142,plain,
    ( spl5_12
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f189,plain,
    ( spl5_17
  <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f199,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl5_9
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f156,f191])).

fof(f191,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f189])).

fof(f156,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f126,f144])).

fof(f144,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f126,plain,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f192,plain,
    ( ~ spl5_5
    | spl5_17
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f181,f142,f189,f100])).

fof(f181,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_12 ),
    inference(superposition,[],[f33,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl5_12 ),
    inference(superposition,[],[f58,f144])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f33,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f168,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f148,f142,f92,f165])).

fof(f92,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f94,f144])).

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f155,plain,
    ( spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f152,f142,f120])).

fof(f120,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f152,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl5_12 ),
    inference(superposition,[],[f74,f144])).

fof(f74,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f37])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f145,plain,
    ( ~ spl5_4
    | spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f133,f129,f142,f92])).

fof(f129,plain,
    ( spl5_10
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f133,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl5_10 ),
    inference(superposition,[],[f131,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f131,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( ~ spl5_3
    | spl5_10
    | spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f97,f92,f82,f129,f87])).

fof(f87,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f94,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f127,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | ~ spl5_1
    | ~ spl5_9
    | spl5_7 ),
    inference(avatar_split_clause,[],[f118,f109,f124,f77,f120,f100])).

fof(f77,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( spl5_7
  <=> r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f118,plain,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_7 ),
    inference(superposition,[],[f111,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f111,plain,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f116,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f36,f106])).

fof(f106,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_6
  <=> v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f112,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f55,f109])).

fof(f55,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f31,f54,f54])).

fof(f31,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f107,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f98,f92,f104,f100])).

fof(f98,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f94,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f95,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f56,f92])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f29,f54])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f57,f87])).

fof(f57,plain,(
    v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f28,f54])).

fof(f28,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f27,f77])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:24:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15356)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (15354)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (15373)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (15376)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (15353)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (15352)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (15380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (15362)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (15355)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (15370)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (15365)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (15368)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (15365)Refutation not found, incomplete strategy% (15365)------------------------------
% 0.22/0.53  % (15365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15365)Memory used [KB]: 1791
% 0.22/0.53  % (15365)Time elapsed: 0.120 s
% 0.22/0.53  % (15365)------------------------------
% 0.22/0.53  % (15365)------------------------------
% 0.22/0.53  % (15357)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (15380)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f107,f112,f116,f127,f132,f145,f155,f168,f192,f204,f213,f216])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ~spl5_5 | spl5_20),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    $false | (~spl5_5 | spl5_20)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f102,f212,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl5_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f210])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    spl5_20 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    v1_relat_1(sK3) | ~spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl5_5 <=> v1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ~spl5_14 | ~spl5_20 | spl5_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f208,f201,f210,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl5_14 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    spl5_19 <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | spl5_19),
% 0.22/0.53    inference(superposition,[],[f203,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | spl5_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f201])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    ~spl5_19 | spl5_9 | ~spl5_12 | ~spl5_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f199,f189,f142,f124,f201])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl5_9 <=> r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl5_12 <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    spl5_17 <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | (spl5_9 | ~spl5_12 | ~spl5_17)),
% 0.22/0.53    inference(forward_demodulation,[],[f156,f191])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl5_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f189])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | (spl5_9 | ~spl5_12)),
% 0.22/0.53    inference(forward_demodulation,[],[f126,f144])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl5_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f142])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | spl5_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f124])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ~spl5_5 | spl5_17 | ~spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f181,f142,f189,f100])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl5_12),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl5_12),
% 0.22/0.53    inference(superposition,[],[f33,f150])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ( ! [X0] : (k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK3)) | ~v1_relat_1(X0)) ) | ~spl5_12),
% 0.22/0.53    inference(superposition,[],[f58,f144])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f34,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f32,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    spl5_14 | ~spl5_4 | ~spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f148,f142,f92,f165])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | (~spl5_4 | ~spl5_12)),
% 0.22/0.53    inference(backward_demodulation,[],[f94,f144])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl5_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f92])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    spl5_8 | ~spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f152,f142,f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl5_8 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl5_12),
% 0.22/0.53    inference(superposition,[],[f74,f144])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.22/0.53    inference(definition_unfolding,[],[f51,f37])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ~spl5_4 | spl5_12 | ~spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f133,f129,f142,f92])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl5_10 <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl5_10),
% 0.22/0.53    inference(superposition,[],[f131,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) | ~spl5_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f129])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ~spl5_3 | spl5_10 | spl5_2 | ~spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f97,f92,f82,f129,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl5_3 <=> v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl5_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3) | ~v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1) | ~spl5_4),
% 0.22/0.53    inference(resolution,[],[f94,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~spl5_5 | ~spl5_8 | ~spl5_1 | ~spl5_9 | spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f118,f109,f124,f77,f120,f100])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl5_1 <=> v1_funct_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl5_7 <=> r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_7),
% 0.22/0.53    inference(superposition,[],[f111,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f39,f54])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl5_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    $false | spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f36,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) | spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl5_6 <=> v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f109])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.22/0.53    inference(definition_unfolding,[],[f31,f54,f54])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl5_5 | ~spl5_6 | ~spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f98,f92,f104,f100])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) | v1_relat_1(sK3) | ~spl5_4),
% 0.22/0.53    inference(resolution,[],[f94,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f92])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f29,f54])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f87])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    v1_funct_2(sK3,k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f28,f54])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f82])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f77])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15380)------------------------------
% 0.22/0.53  % (15380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15380)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15380)Memory used [KB]: 10874
% 0.22/0.53  % (15380)Time elapsed: 0.122 s
% 0.22/0.53  % (15380)------------------------------
% 0.22/0.53  % (15380)------------------------------
% 0.22/0.53  % (15350)Success in time 0.169 s
%------------------------------------------------------------------------------
