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
% DateTime   : Thu Dec  3 12:56:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 192 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  270 ( 448 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f63,f218,f243,f245,f260,f292,f301,f322,f404,f502,f690,f733])).

fof(f733,plain,
    ( spl3_19
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | spl3_19
    | ~ spl3_24 ),
    inference(resolution,[],[f724,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f724,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | spl3_19
    | ~ spl3_24 ),
    inference(resolution,[],[f636,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f636,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_19
    | ~ spl3_24 ),
    inference(resolution,[],[f321,f275])).

fof(f275,plain,
    ( ~ v5_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl3_19
  <=> v5_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f321,plain,
    ( ! [X0] :
        ( v5_relat_1(sK2,X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f690,plain,
    ( spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | spl3_16
    | ~ spl3_17 ),
    inference(resolution,[],[f685,f35])).

fof(f685,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | spl3_16
    | ~ spl3_17 ),
    inference(resolution,[],[f604,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k2_tarski(X1,X0)))
      | ~ r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f604,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_16
    | ~ spl3_17 ),
    inference(resolution,[],[f259,f253])).

fof(f253,plain,
    ( ~ v4_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl3_16
  <=> v4_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f259,plain,
    ( ! [X0] :
        ( v4_relat_1(sK2,X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f502,plain,
    ( ~ spl3_2
    | ~ spl3_19
    | spl3_10 ),
    inference(avatar_split_clause,[],[f498,f215,f273,f58])).

fof(f58,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f215,plain,
    ( spl3_10
  <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f498,plain,
    ( ~ v5_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(resolution,[],[f217,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f217,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f215])).

fof(f404,plain,
    ( ~ spl3_2
    | ~ spl3_16
    | spl3_9 ),
    inference(avatar_split_clause,[],[f400,f211,f251,f58])).

fof(f211,plain,
    ( spl3_9
  <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f400,plain,
    ( ~ v4_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f213,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f213,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f211])).

fof(f322,plain,
    ( ~ spl3_2
    | spl3_24
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f317,f233,f320,f58])).

fof(f233,plain,
    ( spl3_14
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | v5_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_14 ),
    inference(resolution,[],[f234,f72])).

fof(f72,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k2_relat_1(X6),X4)
      | ~ r1_tarski(X4,X5)
      | v5_relat_1(X6,X5)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f234,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f233])).

fof(f301,plain,(
    spl3_21 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl3_21 ),
    inference(resolution,[],[f291,f69])).

fof(f69,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f291,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl3_21
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f292,plain,
    ( ~ spl3_2
    | ~ spl3_21
    | spl3_14 ),
    inference(avatar_split_clause,[],[f286,f233,f289,f58])).

fof(f286,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(resolution,[],[f235,f40])).

fof(f235,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f233])).

fof(f260,plain,
    ( ~ spl3_2
    | spl3_17
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f255,f220,f258,f58])).

fof(f220,plain,
    ( spl3_11
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_11 ),
    inference(resolution,[],[f221,f71])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ r1_tarski(X1,X2)
      | v4_relat_1(X3,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f221,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f220])).

fof(f245,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl3_15 ),
    inference(resolution,[],[f242,f68])).

fof(f68,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f242,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl3_15
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f243,plain,
    ( ~ spl3_2
    | ~ spl3_15
    | spl3_11 ),
    inference(avatar_split_clause,[],[f237,f220,f240,f58])).

fof(f237,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f222,f38])).

fof(f222,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f220])).

fof(f218,plain,
    ( ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f178,f215,f211,f58])).

fof(f178,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f31,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ! [X6,X7] :
      ( r1_tarski(k3_relat_1(X6),X7)
      | ~ r1_tarski(k2_relat_1(X6),X7)
      | ~ r1_tarski(k1_relat_1(X6),X7)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f51,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f32,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f56,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f52,f58,f54])).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:31:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.42  % (19340)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.45  % (19341)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.45  % (19335)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (19342)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.45  % (19331)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (19343)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.46  % (19333)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (19334)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (19339)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.46  % (19337)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (19332)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (19335)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (19336)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.47  % (19346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (19348)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.47  % (19338)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (19344)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f734,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f61,f63,f218,f243,f245,f260,f292,f301,f322,f404,f502,f690,f733])).
% 0.19/0.48  fof(f733,plain,(
% 0.19/0.48    spl3_19 | ~spl3_24),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f731])).
% 0.19/0.48  fof(f731,plain,(
% 0.19/0.48    $false | (spl3_19 | ~spl3_24)),
% 0.19/0.48    inference(resolution,[],[f724,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.48  fof(f724,plain,(
% 0.19/0.48    ~r1_tarski(k4_xboole_0(sK1,sK0),sK1) | (spl3_19 | ~spl3_24)),
% 0.19/0.48    inference(resolution,[],[f636,f50])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.48    inference(definition_unfolding,[],[f42,f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.19/0.48  fof(f636,plain,(
% 0.19/0.48    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))) | (spl3_19 | ~spl3_24)),
% 0.19/0.48    inference(resolution,[],[f321,f275])).
% 0.19/0.48  fof(f275,plain,(
% 0.19/0.48    ~v5_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))) | spl3_19),
% 0.19/0.48    inference(avatar_component_clause,[],[f273])).
% 0.19/0.48  fof(f273,plain,(
% 0.19/0.48    spl3_19 <=> v5_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.19/0.48  fof(f321,plain,(
% 0.19/0.48    ( ! [X0] : (v5_relat_1(sK2,X0) | ~r1_tarski(sK1,X0)) ) | ~spl3_24),
% 0.19/0.48    inference(avatar_component_clause,[],[f320])).
% 0.19/0.48  fof(f320,plain,(
% 0.19/0.48    spl3_24 <=> ! [X0] : (~r1_tarski(sK1,X0) | v5_relat_1(sK2,X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.19/0.48  fof(f690,plain,(
% 0.19/0.48    spl3_16 | ~spl3_17),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f688])).
% 0.19/0.48  fof(f688,plain,(
% 0.19/0.48    $false | (spl3_16 | ~spl3_17)),
% 0.19/0.48    inference(resolution,[],[f685,f35])).
% 0.19/0.48  fof(f685,plain,(
% 0.19/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (spl3_16 | ~spl3_17)),
% 0.19/0.48    inference(resolution,[],[f604,f92])).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k2_tarski(X1,X0))) | ~r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 0.19/0.48    inference(superposition,[],[f50,f49])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.19/0.48    inference(definition_unfolding,[],[f36,f37,f37])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.48  fof(f604,plain,(
% 0.19/0.48    ~r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) | (spl3_16 | ~spl3_17)),
% 0.19/0.48    inference(resolution,[],[f259,f253])).
% 0.19/0.48  fof(f253,plain,(
% 0.19/0.48    ~v4_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))) | spl3_16),
% 0.19/0.48    inference(avatar_component_clause,[],[f251])).
% 0.19/0.48  fof(f251,plain,(
% 0.19/0.48    spl3_16 <=> v4_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.48  fof(f259,plain,(
% 0.19/0.48    ( ! [X0] : (v4_relat_1(sK2,X0) | ~r1_tarski(sK0,X0)) ) | ~spl3_17),
% 0.19/0.48    inference(avatar_component_clause,[],[f258])).
% 0.19/0.48  fof(f258,plain,(
% 0.19/0.48    spl3_17 <=> ! [X0] : (~r1_tarski(sK0,X0) | v4_relat_1(sK2,X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.48  fof(f502,plain,(
% 0.19/0.48    ~spl3_2 | ~spl3_19 | spl3_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f498,f215,f273,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    spl3_2 <=> v1_relat_1(sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f215,plain,(
% 0.19/0.48    spl3_10 <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.48  fof(f498,plain,(
% 0.19/0.48    ~v5_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))) | ~v1_relat_1(sK2) | spl3_10),
% 0.19/0.48    inference(resolution,[],[f217,f40])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.48  fof(f217,plain,(
% 0.19/0.48    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | spl3_10),
% 0.19/0.48    inference(avatar_component_clause,[],[f215])).
% 0.19/0.48  fof(f404,plain,(
% 0.19/0.48    ~spl3_2 | ~spl3_16 | spl3_9),
% 0.19/0.48    inference(avatar_split_clause,[],[f400,f211,f251,f58])).
% 0.19/0.48  fof(f211,plain,(
% 0.19/0.48    spl3_9 <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.48  fof(f400,plain,(
% 0.19/0.48    ~v4_relat_1(sK2,k3_tarski(k2_tarski(sK0,sK1))) | ~v1_relat_1(sK2) | spl3_9),
% 0.19/0.48    inference(resolution,[],[f213,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.48  fof(f213,plain,(
% 0.19/0.48    ~r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | spl3_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f211])).
% 0.19/0.48  fof(f322,plain,(
% 0.19/0.48    ~spl3_2 | spl3_24 | ~spl3_14),
% 0.19/0.48    inference(avatar_split_clause,[],[f317,f233,f320,f58])).
% 0.19/0.48  fof(f233,plain,(
% 0.19/0.48    spl3_14 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.48  fof(f317,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_14),
% 0.19/0.48    inference(resolution,[],[f234,f72])).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    ( ! [X6,X4,X5] : (~r1_tarski(k2_relat_1(X6),X4) | ~r1_tarski(X4,X5) | v5_relat_1(X6,X5) | ~v1_relat_1(X6)) )),
% 0.19/0.48    inference(resolution,[],[f45,f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f29])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.48  fof(f234,plain,(
% 0.19/0.48    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_14),
% 0.19/0.48    inference(avatar_component_clause,[],[f233])).
% 0.19/0.48  fof(f301,plain,(
% 0.19/0.48    spl3_21),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f300])).
% 0.19/0.48  fof(f300,plain,(
% 0.19/0.48    $false | spl3_21),
% 0.19/0.48    inference(resolution,[],[f291,f69])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    v5_relat_1(sK2,sK1)),
% 0.19/0.48    inference(resolution,[],[f44,f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.48    inference(cnf_transformation,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.19/0.48    inference(negated_conjecture,[],[f13])).
% 0.19/0.48  fof(f13,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.48  fof(f291,plain,(
% 0.19/0.48    ~v5_relat_1(sK2,sK1) | spl3_21),
% 0.19/0.48    inference(avatar_component_clause,[],[f289])).
% 0.19/0.48  fof(f289,plain,(
% 0.19/0.48    spl3_21 <=> v5_relat_1(sK2,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.19/0.48  fof(f292,plain,(
% 0.19/0.48    ~spl3_2 | ~spl3_21 | spl3_14),
% 0.19/0.48    inference(avatar_split_clause,[],[f286,f233,f289,f58])).
% 0.19/0.48  fof(f286,plain,(
% 0.19/0.48    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl3_14),
% 0.19/0.48    inference(resolution,[],[f235,f40])).
% 0.19/0.48  fof(f235,plain,(
% 0.19/0.48    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_14),
% 0.19/0.48    inference(avatar_component_clause,[],[f233])).
% 0.19/0.48  fof(f260,plain,(
% 0.19/0.48    ~spl3_2 | spl3_17 | ~spl3_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f255,f220,f258,f58])).
% 0.19/0.48  fof(f220,plain,(
% 0.19/0.48    spl3_11 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.48  fof(f255,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(sK0,X0) | v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl3_11),
% 0.19/0.48    inference(resolution,[],[f221,f71])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    ( ! [X2,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | ~r1_tarski(X1,X2) | v4_relat_1(X3,X2) | ~v1_relat_1(X3)) )),
% 0.19/0.48    inference(resolution,[],[f45,f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  fof(f221,plain,(
% 0.19/0.48    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f220])).
% 0.19/0.48  fof(f245,plain,(
% 0.19/0.48    spl3_15),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f244])).
% 0.19/0.48  fof(f244,plain,(
% 0.19/0.48    $false | spl3_15),
% 0.19/0.48    inference(resolution,[],[f242,f68])).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    v4_relat_1(sK2,sK0)),
% 0.19/0.48    inference(resolution,[],[f43,f30])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f242,plain,(
% 0.19/0.48    ~v4_relat_1(sK2,sK0) | spl3_15),
% 0.19/0.48    inference(avatar_component_clause,[],[f240])).
% 0.19/0.48  fof(f240,plain,(
% 0.19/0.48    spl3_15 <=> v4_relat_1(sK2,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.48  fof(f243,plain,(
% 0.19/0.48    ~spl3_2 | ~spl3_15 | spl3_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f237,f220,f240,f58])).
% 0.19/0.48  fof(f237,plain,(
% 0.19/0.48    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_11),
% 0.19/0.48    inference(resolution,[],[f222,f38])).
% 0.19/0.48  fof(f222,plain,(
% 0.19/0.48    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f220])).
% 0.19/0.48  fof(f218,plain,(
% 0.19/0.48    ~spl3_2 | ~spl3_9 | ~spl3_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f178,f215,f211,f58])).
% 0.19/0.48  fof(f178,plain,(
% 0.19/0.48    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | ~v1_relat_1(sK2)),
% 0.19/0.48    inference(resolution,[],[f103,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.19/0.48    inference(definition_unfolding,[],[f31,f37])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.19/0.48    inference(cnf_transformation,[],[f27])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    ( ! [X6,X7] : (r1_tarski(k3_relat_1(X6),X7) | ~r1_tarski(k2_relat_1(X6),X7) | ~r1_tarski(k1_relat_1(X6),X7) | ~v1_relat_1(X6)) )),
% 0.19/0.48    inference(superposition,[],[f51,f48])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(definition_unfolding,[],[f32,f37])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(definition_unfolding,[],[f46,f37])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    spl3_1),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f62])).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    $false | spl3_1),
% 0.19/0.48    inference(resolution,[],[f56,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,axiom,(
% 0.19/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    spl3_1 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    ~spl3_1 | spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f52,f58,f54])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f33,f30])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (19335)------------------------------
% 0.19/0.48  % (19335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (19335)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (19335)Memory used [KB]: 6396
% 0.19/0.48  % (19335)Time elapsed: 0.065 s
% 0.19/0.48  % (19335)------------------------------
% 0.19/0.48  % (19335)------------------------------
% 0.19/0.48  % (19345)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.48  % (19330)Success in time 0.135 s
%------------------------------------------------------------------------------
