%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 190 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  256 ( 389 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f81,f120,f128,f193,f199,f207,f211,f239])).

fof(f239,plain,
    ( ~ spl3_4
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl3_4
    | spl3_12 ),
    inference(resolution,[],[f208,f108])).

fof(f108,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f64,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f60,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

% (24932)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f208,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_4
    | spl3_12 ),
    inference(resolution,[],[f206,f130])).

fof(f130,plain,
    ( ! [X1] :
        ( v5_relat_1(sK2,X1)
        | ~ r1_tarski(sK1,X1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f127,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k2_zfmisc_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f56,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f127,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k2_zfmisc_1(sK0,sK1),X0)
        | v5_relat_1(sK2,X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_4
  <=> ! [X0] :
        ( v5_relat_1(sK2,X0)
        | ~ v5_relat_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f206,plain,
    ( ~ v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_12
  <=> v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f211,plain,
    ( ~ spl3_3
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl3_3
    | spl3_11 ),
    inference(resolution,[],[f200,f64])).

fof(f200,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_3
    | spl3_11 ),
    inference(resolution,[],[f198,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( v4_relat_1(sK2,X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f119,f103])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( v4_relat_1(k2_zfmisc_1(X3,X5),X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f55,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k2_zfmisc_1(sK0,sK1),X0)
        | v4_relat_1(sK2,X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_3
  <=> ! [X0] :
        ( v4_relat_1(sK2,X0)
        | ~ v4_relat_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f198,plain,
    ( ~ v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_11
  <=> v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f207,plain,
    ( ~ spl3_2
    | ~ spl3_12
    | spl3_10 ),
    inference(avatar_split_clause,[],[f202,f190,f204,f76])).

fof(f76,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f190,plain,
    ( spl3_10
  <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f202,plain,
    ( ~ v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(resolution,[],[f192,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f192,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f199,plain,
    ( ~ spl3_2
    | ~ spl3_11
    | spl3_9 ),
    inference(avatar_split_clause,[],[f194,f186,f196,f76])).

fof(f186,plain,
    ( spl3_9
  <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f194,plain,
    ( ~ v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f188,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f188,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f193,plain,
    ( ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f181,f190,f186,f76])).

fof(f181,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f142,f62])).

fof(f62,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f38,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f142,plain,(
    ! [X2,X3] :
      ( r1_tarski(k3_relat_1(X2),X3)
      | ~ r1_tarski(k2_relat_1(X2),X3)
      | ~ r1_tarski(k1_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f66,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f39,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f128,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f123,f126,f72])).

fof(f72,plain,
    ( spl3_1
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f123,plain,(
    ! [X0] :
      ( v5_relat_1(sK2,X0)
      | ~ v5_relat_1(k2_zfmisc_1(sK0,sK1),X0)
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v5_relat_1(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(f120,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f115,f118,f72])).

fof(f115,plain,(
    ! [X0] :
      ( v4_relat_1(sK2,X0)
      | ~ v4_relat_1(k2_zfmisc_1(sK0,sK1),X0)
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v4_relat_1(X2,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(f81,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f74,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f69,f76,f72])).

fof(f69,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f40,f37])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (24927)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (24925)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24928)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (24937)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (24927)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f79,f81,f120,f128,f193,f199,f207,f211,f239])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ~spl3_4 | spl3_12),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    $false | (~spl3_4 | spl3_12)),
% 0.21/0.47    inference(resolution,[],[f208,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.21/0.47    inference(superposition,[],[f64,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f43,f60,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f44,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  % (24932)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f45,f60])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | (~spl3_4 | spl3_12)),
% 0.21/0.47    inference(resolution,[],[f206,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X1] : (v5_relat_1(sK2,X1) | ~r1_tarski(sK1,X1)) ) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f127,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v5_relat_1(k2_zfmisc_1(X2,X0),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f56,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f58,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X0] : (~v5_relat_1(k2_zfmisc_1(sK0,sK1),X0) | v5_relat_1(sK2,X0)) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f126])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    spl3_4 <=> ! [X0] : (v5_relat_1(sK2,X0) | ~v5_relat_1(k2_zfmisc_1(sK0,sK1),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    ~v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f204])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    spl3_12 <=> v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ~spl3_3 | spl3_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f210])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    $false | (~spl3_3 | spl3_11)),
% 0.21/0.47    inference(resolution,[],[f200,f64])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    ~r1_tarski(sK0,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | (~spl3_3 | spl3_11)),
% 0.21/0.47    inference(resolution,[],[f198,f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0] : (v4_relat_1(sK2,X0) | ~r1_tarski(sK0,X0)) ) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f119,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (v4_relat_1(k2_zfmisc_1(X3,X5),X4) | ~r1_tarski(X3,X4)) )),
% 0.21/0.47    inference(resolution,[],[f55,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f57,f53])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0] : (~v4_relat_1(k2_zfmisc_1(sK0,sK1),X0) | v4_relat_1(sK2,X0)) ) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl3_3 <=> ! [X0] : (v4_relat_1(sK2,X0) | ~v4_relat_1(k2_zfmisc_1(sK0,sK1),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    ~v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f196])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    spl3_11 <=> v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ~spl3_2 | ~spl3_12 | spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f202,f190,f204,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_2 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl3_10 <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    ~v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | ~v1_relat_1(sK2) | spl3_10),
% 0.21/0.47    inference(resolution,[],[f192,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f190])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    ~spl3_2 | ~spl3_11 | spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f194,f186,f196,f76])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    spl3_9 <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    ~v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | ~v1_relat_1(sK2) | spl3_9),
% 0.21/0.47    inference(resolution,[],[f188,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f186])).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    ~spl3_2 | ~spl3_9 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f181,f190,f186,f76])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) | ~v1_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f142,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f38,f61])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f17])).
% 0.21/0.47  fof(f17,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r1_tarski(k3_relat_1(X2),X3) | ~r1_tarski(k2_relat_1(X2),X3) | ~r1_tarski(k1_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(superposition,[],[f66,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f39,f61])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f59,f61])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ~spl3_1 | spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f123,f126,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl3_1 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X0] : (v5_relat_1(sK2,X0) | ~v5_relat_1(k2_zfmisc_1(sK0,sK1),X0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.47    inference(resolution,[],[f51,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | v5_relat_1(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~spl3_1 | spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f115,f118,f72])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0] : (v4_relat_1(sK2,X0) | ~v4_relat_1(k2_zfmisc_1(sK0,sK1),X0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.47    inference(resolution,[],[f50,f37])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | v4_relat_1(X2,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    $false | spl3_1),
% 0.21/0.47    inference(resolution,[],[f74,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f69,f76,f72])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    inference(resolution,[],[f40,f37])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24927)------------------------------
% 0.21/0.47  % (24927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24927)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24927)Memory used [KB]: 6140
% 0.21/0.47  % (24927)Time elapsed: 0.057 s
% 0.21/0.47  % (24927)------------------------------
% 0.21/0.47  % (24927)------------------------------
% 0.21/0.47  % (24926)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (24922)Success in time 0.113 s
%------------------------------------------------------------------------------
