%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 141 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 419 expanded)
%              Number of equality atoms :   31 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f70,f74,f78,f84,f94,f98,f102,f111,f114])).

fof(f114,plain,
    ( ~ spl2_5
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f112,f89])).

fof(f89,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_9
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f112,plain,
    ( ~ v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(superposition,[],[f69,f110])).

fof(f110,plain,
    ( k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_12
  <=> k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f69,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_5
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f111,plain,
    ( spl2_12
    | spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f106,f100,f58,f48,f108])).

fof(f48,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f58,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f100,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f106,plain,
    ( k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f103,f50])).

fof(f50,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f103,plain,
    ( k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f101,f60])).

fof(f60,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f46,f100])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f98,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_6
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_6
    | spl2_10 ),
    inference(subsumption_resolution,[],[f96,f50])).

fof(f96,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_6
    | spl2_10 ),
    inference(subsumption_resolution,[],[f95,f60])).

fof(f95,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_6
    | spl2_10 ),
    inference(resolution,[],[f93,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f93,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_10
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f94,plain,
    ( spl2_9
    | ~ spl2_10
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f85,f82,f63,f91,f87])).

fof(f63,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f82,plain,
    ( spl2_8
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f85,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl2_8
    | spl2_1
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f80,f76,f53,f48,f82])).

fof(f53,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_subset_1(X0,sK0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f79,f50])).

fof(f79,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f74,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f70,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f39,f68])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~ v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

fof(f66,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (4731)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.42  % (4731)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f70,f74,f78,f84,f94,f98,f102,f111,f114])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ~spl2_5 | ~spl2_9 | ~spl2_12),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    $false | (~spl2_5 | ~spl2_9 | ~spl2_12)),
% 0.20/0.42    inference(subsumption_resolution,[],[f112,f89])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl2_9 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    ~v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl2_5 | ~spl2_12)),
% 0.20/0.42    inference(superposition,[],[f69,f110])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f108])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    spl2_12 <=> k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f68])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_5 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : ~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f111,plain,(
% 0.20/0.42    spl2_12 | spl2_1 | ~spl2_3 | ~spl2_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f106,f100,f58,f48,f108])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl2_1 <=> v1_xboole_0(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    spl2_11 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (spl2_1 | ~spl2_3 | ~spl2_11)),
% 0.20/0.42    inference(subsumption_resolution,[],[f103,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f48])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | v1_xboole_0(sK0) | (~spl2_3 | ~spl2_11)),
% 0.20/0.42    inference(resolution,[],[f101,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f58])).
% 0.20/0.42  fof(f101,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) ) | ~spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f100])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    spl2_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f46,f100])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f32,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f29,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f31,f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f34,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f35,f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f36,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f37,f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,axiom,(
% 0.20/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    spl2_1 | ~spl2_3 | ~spl2_6 | spl2_10),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f97])).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    $false | (spl2_1 | ~spl2_3 | ~spl2_6 | spl2_10)),
% 0.20/0.42    inference(subsumption_resolution,[],[f96,f50])).
% 0.20/0.42  fof(f96,plain,(
% 0.20/0.42    v1_xboole_0(sK0) | (~spl2_3 | ~spl2_6 | spl2_10)),
% 0.20/0.42    inference(subsumption_resolution,[],[f95,f60])).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_6 | spl2_10)),
% 0.20/0.42    inference(resolution,[],[f93,f73])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    spl2_6 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f91])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    spl2_10 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    spl2_9 | ~spl2_10 | ~spl2_4 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f85,f82,f63,f91,f87])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl2_8 <=> ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl2_4 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f83,f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f63])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0)) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f82])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl2_8 | spl2_1 | ~spl2_2 | ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f80,f76,f53,f48,f82])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl2_7 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0)) ) | (spl2_1 | ~spl2_2 | ~spl2_7)),
% 0.20/0.42    inference(subsumption_resolution,[],[f79,f50])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0) | v1_xboole_0(sK0)) ) | (~spl2_2 | ~spl2_7)),
% 0.20/0.42    inference(resolution,[],[f77,f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f76])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f76])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,axiom,(
% 0.20/0.42    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f33,f72])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f39,f68])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~v1_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f63])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.42    inference(negated_conjecture,[],[f12])).
% 0.20/0.42  fof(f12,conjecture,(
% 0.20/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f58])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    m1_subset_1(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f53])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    v1_zfmisc_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f48])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~v1_xboole_0(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (4731)------------------------------
% 0.20/0.42  % (4731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (4731)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (4731)Memory used [KB]: 6140
% 0.20/0.42  % (4731)Time elapsed: 0.007 s
% 0.20/0.42  % (4731)------------------------------
% 0.20/0.42  % (4731)------------------------------
% 0.20/0.43  % (4722)Success in time 0.065 s
%------------------------------------------------------------------------------
