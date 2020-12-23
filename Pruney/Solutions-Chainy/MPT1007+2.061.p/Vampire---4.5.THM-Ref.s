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
% DateTime   : Thu Dec  3 13:04:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 224 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :    8
%              Number of atoms          :  325 ( 733 expanded)
%              Number of equality atoms :   55 ( 169 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f83,f88,f96,f105,f113,f118,f135,f144,f148,f152,f159,f179,f180])).

fof(f180,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f179,plain,
    ( spl4_20
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f160,f156,f116,f176])).

fof(f176,plain,
    ( spl4_20
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f116,plain,
    ( spl4_10
  <=> ! [X0] :
        ( sK0 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f156,plain,
    ( spl4_16
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f160,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(resolution,[],[f158,f117])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f158,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( ~ spl4_6
    | ~ spl4_1
    | spl4_16
    | spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f153,f141,f102,f156,f63,f93])).

fof(f93,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f63,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f102,plain,
    ( spl4_8
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f141,plain,
    ( spl4_15
  <=> r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f153,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(superposition,[],[f143,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f143,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f152,plain,
    ( ~ spl4_7
    | spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f149,f133,f73,f98])).

fof(f98,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f73,plain,
    ( spl4_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f133,plain,
    ( spl4_13
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f149,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f134,f75])).

fof(f75,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f148,plain,(
    ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f54,f139])).

fof(f139,plain,
    ( v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_14
  <=> v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f54,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f144,plain,
    ( spl4_14
    | spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f131,f111,f141,f137])).

fof(f111,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f131,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f112,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f135,plain,
    ( ~ spl4_6
    | ~ spl4_1
    | spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f114,f85,f133,f63,f93])).

fof(f85,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f114,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | r2_hidden(X3,sK1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | r2_hidden(X1,X3) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f91,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f118,plain,
    ( ~ spl4_6
    | ~ spl4_1
    | spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f109,f85,f116,f63,f93])).

fof(f109,plain,
    ( ! [X0] :
        ( sK0 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f106,f60])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | spl4_9
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f89,f85,f68,f111,f80,f63])).

fof(f80,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f68,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f105,plain,
    ( ~ spl4_6
    | ~ spl4_1
    | spl4_7
    | ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f77,f73,f102,f98,f63,f93])).

fof(f77,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(superposition,[],[f75,f59])).

fof(f96,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f90,f85,f93])).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f88,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f52,f85])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f51])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f80])).

fof(f53,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n007.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 12:11:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.48  % (2057)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.49  % (2049)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.49  % (2049)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f181,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f66,f71,f76,f83,f88,f96,f105,f113,f118,f135,f144,f148,f152,f159,f179,f180])).
% 0.23/0.49  fof(f180,plain,(
% 0.23/0.49    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.23/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.49  fof(f179,plain,(
% 0.23/0.49    spl4_20 | ~spl4_10 | ~spl4_16),
% 0.23/0.49    inference(avatar_split_clause,[],[f160,f156,f116,f176])).
% 0.23/0.49  fof(f176,plain,(
% 0.23/0.49    spl4_20 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.23/0.49  fof(f116,plain,(
% 0.23/0.49    spl4_10 <=> ! [X0] : (sK0 = X0 | ~r2_hidden(X0,k1_relat_1(sK2)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.49  fof(f156,plain,(
% 0.23/0.49    spl4_16 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.23/0.49  fof(f160,plain,(
% 0.23/0.49    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl4_10 | ~spl4_16)),
% 0.23/0.49    inference(resolution,[],[f158,f117])).
% 0.23/0.49  fof(f117,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl4_10),
% 0.23/0.49    inference(avatar_component_clause,[],[f116])).
% 0.23/0.49  fof(f158,plain,(
% 0.23/0.49    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2)) | ~spl4_16),
% 0.23/0.49    inference(avatar_component_clause,[],[f156])).
% 0.23/0.49  fof(f159,plain,(
% 0.23/0.49    ~spl4_6 | ~spl4_1 | spl4_16 | spl4_8 | ~spl4_15),
% 0.23/0.49    inference(avatar_split_clause,[],[f153,f141,f102,f156,f63,f93])).
% 0.23/0.49  fof(f93,plain,(
% 0.23/0.49    spl4_6 <=> v1_relat_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.49  fof(f63,plain,(
% 0.23/0.49    spl4_1 <=> v1_funct_1(sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.49  fof(f102,plain,(
% 0.23/0.49    spl4_8 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.23/0.49  fof(f141,plain,(
% 0.23/0.49    spl4_15 <=> r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.23/0.49  fof(f153,plain,(
% 0.23/0.49    r2_hidden(k1_xboole_0,sK1) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_15),
% 0.23/0.49    inference(superposition,[],[f143,f59])).
% 0.23/0.49  fof(f59,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.49    inference(equality_resolution,[],[f38])).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.49    inference(nnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.49    inference(flattening,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,axiom,(
% 0.23/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.23/0.49  fof(f143,plain,(
% 0.23/0.49    r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | ~spl4_15),
% 0.23/0.49    inference(avatar_component_clause,[],[f141])).
% 0.23/0.49  fof(f152,plain,(
% 0.23/0.49    ~spl4_7 | spl4_3 | ~spl4_13),
% 0.23/0.49    inference(avatar_split_clause,[],[f149,f133,f73,f98])).
% 0.23/0.49  fof(f98,plain,(
% 0.23/0.49    spl4_7 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    spl4_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.49  fof(f133,plain,(
% 0.23/0.49    spl4_13 <=> ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.23/0.49  fof(f149,plain,(
% 0.23/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | (spl4_3 | ~spl4_13)),
% 0.23/0.49    inference(resolution,[],[f134,f75])).
% 0.23/0.49  fof(f75,plain,(
% 0.23/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl4_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f73])).
% 0.23/0.49  fof(f134,plain,(
% 0.23/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl4_13),
% 0.23/0.49    inference(avatar_component_clause,[],[f133])).
% 0.23/0.49  fof(f148,plain,(
% 0.23/0.49    ~spl4_14),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f145])).
% 0.23/0.49  fof(f145,plain,(
% 0.23/0.49    $false | ~spl4_14),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f54,f139])).
% 0.23/0.49  fof(f139,plain,(
% 0.23/0.49    v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_14),
% 0.23/0.49    inference(avatar_component_clause,[],[f137])).
% 0.23/0.49  fof(f137,plain,(
% 0.23/0.49    spl4_14 <=> v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f41,f50])).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f42,f44])).
% 0.23/0.49  fof(f44,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.23/0.49  fof(f144,plain,(
% 0.23/0.49    spl4_14 | spl4_15 | ~spl4_9),
% 0.23/0.49    inference(avatar_split_clause,[],[f131,f111,f141,f137])).
% 0.23/0.49  fof(f111,plain,(
% 0.23/0.49    spl4_9 <=> ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.49  fof(f131,plain,(
% 0.23/0.49    r2_hidden(k1_funct_1(sK2,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_9),
% 0.23/0.49    inference(resolution,[],[f112,f40])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.23/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.49  fof(f112,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl4_9),
% 0.23/0.49    inference(avatar_component_clause,[],[f111])).
% 0.23/0.49  fof(f135,plain,(
% 0.23/0.49    ~spl4_6 | ~spl4_1 | spl4_13 | ~spl4_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f114,f85,f133,f63,f93])).
% 0.23/0.49  fof(f85,plain,(
% 0.23/0.49    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.49  fof(f114,plain,(
% 0.23/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f107,f60])).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.49    inference(equality_resolution,[],[f36])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f107,plain,(
% 0.23/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | r2_hidden(X3,sK1)) ) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f91,f56])).
% 0.23/0.49  fof(f56,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | r2_hidden(X1,X3)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f48,f51])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f35,f50])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.23/0.49    inference(flattening,[],[f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.23/0.49    inference(nnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.23/0.49  fof(f91,plain,(
% 0.23/0.49    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f87,f43])).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.23/0.49  fof(f87,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl4_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f85])).
% 0.23/0.49  fof(f118,plain,(
% 0.23/0.49    ~spl4_6 | ~spl4_1 | spl4_10 | ~spl4_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f109,f85,f116,f63,f93])).
% 0.23/0.49  fof(f109,plain,(
% 0.23/0.49    ( ! [X0] : (sK0 = X0 | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f106,f60])).
% 0.23/0.49  fof(f106,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f91,f57])).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 0.23/0.49    inference(definition_unfolding,[],[f47,f51])).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f29])).
% 0.23/0.49  fof(f113,plain,(
% 0.23/0.49    ~spl4_1 | ~spl4_4 | spl4_9 | spl4_2 | ~spl4_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f89,f85,f68,f111,f80,f63])).
% 0.23/0.49  fof(f80,plain,(
% 0.23/0.49    spl4_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.49  fof(f68,plain,(
% 0.23/0.49    spl4_2 <=> k1_xboole_0 = sK1),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.49  fof(f89,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2)) ) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f87,f46])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.23/0.49    inference(flattening,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.23/0.49    inference(ennf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.23/0.49  fof(f105,plain,(
% 0.23/0.49    ~spl4_6 | ~spl4_1 | spl4_7 | ~spl4_8 | spl4_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f77,f73,f102,f98,f63,f93])).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    ~r2_hidden(k1_xboole_0,sK1) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_3),
% 0.23/0.49    inference(superposition,[],[f75,f59])).
% 0.23/0.49  fof(f96,plain,(
% 0.23/0.49    spl4_6 | ~spl4_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f90,f85,f93])).
% 0.23/0.49  fof(f90,plain,(
% 0.23/0.49    v1_relat_1(sK2) | ~spl4_5),
% 0.23/0.49    inference(resolution,[],[f87,f45])).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(ennf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.49  fof(f88,plain,(
% 0.23/0.49    spl4_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f52,f85])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.23/0.49    inference(definition_unfolding,[],[f32,f51])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.23/0.49    inference(flattening,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.23/0.49    inference(ennf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.23/0.49    inference(negated_conjecture,[],[f11])).
% 0.23/0.49  fof(f11,conjecture,(
% 0.23/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.23/0.49  fof(f83,plain,(
% 0.23/0.49    spl4_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f53,f80])).
% 0.23/0.49  fof(f53,plain,(
% 0.23/0.49    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.23/0.49    inference(definition_unfolding,[],[f31,f51])).
% 0.23/0.49  fof(f31,plain,(
% 0.23/0.49    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f76,plain,(
% 0.23/0.49    ~spl4_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f34,f73])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f71,plain,(
% 0.23/0.49    ~spl4_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f33,f68])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    k1_xboole_0 != sK1),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    spl4_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f30,f63])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    v1_funct_1(sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (2049)------------------------------
% 0.23/0.49  % (2049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (2049)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (2049)Memory used [KB]: 10746
% 0.23/0.49  % (2049)Time elapsed: 0.068 s
% 0.23/0.49  % (2049)------------------------------
% 0.23/0.49  % (2049)------------------------------
% 0.23/0.50  % (2038)Success in time 0.122 s
%------------------------------------------------------------------------------
