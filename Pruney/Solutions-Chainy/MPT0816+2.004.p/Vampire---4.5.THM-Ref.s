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
% DateTime   : Thu Dec  3 12:56:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 157 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :  246 ( 445 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f51,f55,f59,f67,f71,f75,f81,f110,f116,f121,f131,f174,f206,f216,f223,f234])).

fof(f234,plain,
    ( ~ spl3_3
    | spl3_12
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl3_3
    | spl3_12
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f232,f80])).

fof(f80,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_12
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f232,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(resolution,[],[f222,f41])).

fof(f41,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_3
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | r1_tarski(sK2,k2_zfmisc_1(X0,sK1)) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_39
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | r1_tarski(sK2,k2_zfmisc_1(X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f223,plain,
    ( spl3_39
    | ~ spl3_21
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f217,f214,f129,f221])).

fof(f129,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0)
        | r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f214,plain,
    ( spl3_38
  <=> ! [X3,X2] :
        ( r1_tarski(k2_zfmisc_1(X2,k2_relat_1(sK2)),k2_zfmisc_1(X3,sK1))
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | r1_tarski(sK2,k2_zfmisc_1(X0,sK1)) )
    | ~ spl3_21
    | ~ spl3_38 ),
    inference(resolution,[],[f215,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f129])).

fof(f215,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X2,k2_relat_1(sK2)),k2_zfmisc_1(X3,sK1))
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl3_38
    | ~ spl3_10
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f208,f204,f69,f214])).

fof(f69,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f204,plain,
    ( spl3_36
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),X1)
        | r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f208,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X2,k2_relat_1(sK2)),k2_zfmisc_1(X3,sK1))
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_10
    | ~ spl3_36 ),
    inference(resolution,[],[f205,f70])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),X1)
        | r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl3_36
    | ~ spl3_11
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f202,f172,f73,f204])).

fof(f73,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f172,plain,
    ( spl3_29
  <=> ! [X9] : k2_zfmisc_1(X9,sK1) = k2_xboole_0(k2_zfmisc_1(X9,k2_relat_1(sK2)),k2_zfmisc_1(X9,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),X1)
        | r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1) )
    | ~ spl3_11
    | ~ spl3_29 ),
    inference(superposition,[],[f74,f173])).

fof(f173,plain,
    ( ! [X9] : k2_zfmisc_1(X9,sK1) = k2_xboole_0(k2_zfmisc_1(X9,k2_relat_1(sK2)),k2_zfmisc_1(X9,sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f172])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f174,plain,
    ( spl3_29
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f155,f119,f34,f172])).

fof(f34,plain,
    ( spl3_2
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f119,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f155,plain,
    ( ! [X9] : k2_zfmisc_1(X9,sK1) = k2_xboole_0(k2_zfmisc_1(X9,k2_relat_1(sK2)),k2_zfmisc_1(X9,sK1))
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f120,f36])).

fof(f36,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f131,plain,
    ( spl3_21
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f127,f113,f73,f129])).

fof(f113,plain,
    ( spl3_18
  <=> k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(superposition,[],[f74,f115])).

fof(f115,plain,
    ( k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f121,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f117,f65,f53,f119])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f116,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f111,f107,f53,f113])).

fof(f107,plain,
    ( spl3_17
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f111,plain,
    ( k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(resolution,[],[f109,f54])).

fof(f109,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f105,f49,f44,f107])).

fof(f44,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(resolution,[],[f50,f46])).

fof(f46,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f81,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f57,f29,f78])).

fof(f29,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f58,f31])).

fof(f31,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f75,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f71,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f25,f69])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f67,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & r1_tarski(k2_relat_1(sK2),sK1)
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & r1_tarski(k2_relat_1(X2),X1)
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & r1_tarski(k2_relat_1(sK2),sK1)
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k2_relat_1(X2),X1)
            & r1_tarski(k1_relat_1(X2),X0) )
         => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (20402)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (20397)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.45  % (20396)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.45  % (20404)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.45  % (20400)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (20399)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.45  % (20403)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.46  % (20405)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.46  % (20400)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f51,f55,f59,f67,f71,f75,f81,f110,f116,f121,f131,f174,f206,f216,f223,f234])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ~spl3_3 | spl3_12 | ~spl3_39),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    $false | (~spl3_3 | spl3_12 | ~spl3_39)),
% 0.21/0.46    inference(subsumption_resolution,[],[f232,f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl3_12 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | (~spl3_3 | ~spl3_39)),
% 0.21/0.46    inference(resolution,[],[f222,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl3_3 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | r1_tarski(sK2,k2_zfmisc_1(X0,sK1))) ) | ~spl3_39),
% 0.21/0.46    inference(avatar_component_clause,[],[f221])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl3_39 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | r1_tarski(sK2,k2_zfmisc_1(X0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    spl3_39 | ~spl3_21 | ~spl3_38),
% 0.21/0.46    inference(avatar_split_clause,[],[f217,f214,f129,f221])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl3_21 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0) | r1_tarski(sK2,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    spl3_38 <=> ! [X3,X2] : (r1_tarski(k2_zfmisc_1(X2,k2_relat_1(sK2)),k2_zfmisc_1(X3,sK1)) | ~r1_tarski(X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | r1_tarski(sK2,k2_zfmisc_1(X0,sK1))) ) | (~spl3_21 | ~spl3_38)),
% 0.21/0.46    inference(resolution,[],[f215,f130])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0) | r1_tarski(sK2,X0)) ) | ~spl3_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X2,k2_relat_1(sK2)),k2_zfmisc_1(X3,sK1)) | ~r1_tarski(X2,X3)) ) | ~spl3_38),
% 0.21/0.46    inference(avatar_component_clause,[],[f214])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    spl3_38 | ~spl3_10 | ~spl3_36),
% 0.21/0.46    inference(avatar_split_clause,[],[f208,f204,f69,f214])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    spl3_36 <=> ! [X1,X0] : (~r1_tarski(k2_zfmisc_1(X0,sK1),X1) | r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.46  fof(f208,plain,(
% 0.21/0.46    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X2,k2_relat_1(sK2)),k2_zfmisc_1(X3,sK1)) | ~r1_tarski(X2,X3)) ) | (~spl3_10 | ~spl3_36)),
% 0.21/0.46    inference(resolution,[],[f205,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),X1) | r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1)) ) | ~spl3_36),
% 0.21/0.46    inference(avatar_component_clause,[],[f204])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    spl3_36 | ~spl3_11 | ~spl3_29),
% 0.21/0.46    inference(avatar_split_clause,[],[f202,f172,f73,f204])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    spl3_29 <=> ! [X9] : k2_zfmisc_1(X9,sK1) = k2_xboole_0(k2_zfmisc_1(X9,k2_relat_1(sK2)),k2_zfmisc_1(X9,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),X1) | r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1)) ) | (~spl3_11 | ~spl3_29)),
% 0.21/0.46    inference(superposition,[],[f74,f173])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    ( ! [X9] : (k2_zfmisc_1(X9,sK1) = k2_xboole_0(k2_zfmisc_1(X9,k2_relat_1(sK2)),k2_zfmisc_1(X9,sK1))) ) | ~spl3_29),
% 0.21/0.46    inference(avatar_component_clause,[],[f172])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    spl3_29 | ~spl3_2 | ~spl3_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f155,f119,f34,f172])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl3_2 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    spl3_19 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    ( ! [X9] : (k2_zfmisc_1(X9,sK1) = k2_xboole_0(k2_zfmisc_1(X9,k2_relat_1(sK2)),k2_zfmisc_1(X9,sK1))) ) | (~spl3_2 | ~spl3_19)),
% 0.21/0.46    inference(resolution,[],[f120,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ) | ~spl3_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f119])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl3_21 | ~spl3_11 | ~spl3_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f127,f113,f73,f129])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl3_18 <=> k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0) | r1_tarski(sK2,X0)) ) | (~spl3_11 | ~spl3_18)),
% 0.21/0.46    inference(superposition,[],[f74,f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f113])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl3_19 | ~spl3_6 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f117,f65,f53,f119])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl3_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X1) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.46    inference(resolution,[],[f66,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f53])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f65])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    spl3_18 | ~spl3_6 | ~spl3_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f111,f107,f53,f113])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl3_17 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl3_6 | ~spl3_17)),
% 0.21/0.46    inference(resolution,[],[f109,f54])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f107])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl3_17 | ~spl3_4 | ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f105,f49,f44,f107])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl3_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl3_4 | ~spl3_5)),
% 0.21/0.46    inference(resolution,[],[f50,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ~spl3_12 | spl3_1 | ~spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f76,f57,f29,f78])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl3_7 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | (spl3_1 | ~spl3_7)),
% 0.21/0.46    inference(resolution,[],[f58,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f29])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f73])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f69])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f44])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & r1_tarski(k2_relat_1(sK2),sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) => (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & r1_tarski(k2_relat_1(sK2),sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & (r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f39])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f29])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (20400)------------------------------
% 0.21/0.46  % (20400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20400)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (20400)Memory used [KB]: 10618
% 0.21/0.46  % (20400)Time elapsed: 0.045 s
% 0.21/0.46  % (20400)------------------------------
% 0.21/0.46  % (20400)------------------------------
% 0.21/0.46  % (20395)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % (20394)Success in time 0.099 s
%------------------------------------------------------------------------------
