%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 131 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 ( 339 expanded)
%              Number of equality atoms :  110 ( 135 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f82,f104,f133,f178,f249,f273,f310,f391,f398,f407])).

fof(f407,plain,
    ( spl3_3
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl3_3
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f81,f35,f397,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f397,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl3_28
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f81,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f398,plain,
    ( spl3_28
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f394,f388,f69,f396])).

fof(f69,plain,
    ( spl3_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f388,plain,
    ( spl3_27
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f394,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f392,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f392,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0))
    | ~ spl3_27 ),
    inference(resolution,[],[f390,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f390,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f388])).

fof(f391,plain,
    ( spl3_27
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f385,f131,f388])).

fof(f131,plain,
    ( spl3_9
  <=> ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f385,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(resolution,[],[f85,f132])).

fof(f132,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f85,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_tarski(k4_tarski(X6,X7),k4_tarski(X8,X9))))
      | v1_relat_1(X5) ) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f58,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f310,plain,
    ( spl3_3
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl3_3
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f81,f272])).

fof(f272,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_18
  <=> ! [X1,X0] : X0 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f273,plain,
    ( spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f260,f247,f271])).

fof(f247,plain,
    ( spl3_14
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f260,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl3_14 ),
    inference(superposition,[],[f248,f248])).

fof(f248,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f227,f176,f101,f247])).

fof(f101,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f176,plain,
    ( spl3_11
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f227,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f137,f177])).

fof(f177,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0))
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(superposition,[],[f42,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f178,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f174,f101,f176])).

fof(f174,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_5 ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )
    | ~ spl3_5 ),
    inference(superposition,[],[f129,f103])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(X0),X1) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | k3_xboole_0(X0,X1) = k1_tarski(X2)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(superposition,[],[f67,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f133,plain,
    ( spl3_9
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f128,f101,f98,f131])).

fof(f98,plain,
    ( spl3_4
  <=> ! [X0] : k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f127,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f127,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f126,f102])).

fof(f102,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f126,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl3_4 ),
    inference(superposition,[],[f40,f99])).

fof(f99,plain,
    ( ! [X0] : k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f104,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f96,f101,f98])).

fof(f96,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(k1_xboole_0)
      | k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f90,f36])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | k1_xboole_0 = k1_tarski(X0)
      | sK1(X1,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).

fof(f22,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f72,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (18036)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.48  % (18024)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.48  % (18024)Refutation not found, incomplete strategy% (18024)------------------------------
% 0.22/0.48  % (18024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18024)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (18024)Memory used [KB]: 10490
% 0.22/0.48  % (18024)Time elapsed: 0.049 s
% 0.22/0.48  % (18024)------------------------------
% 0.22/0.48  % (18024)------------------------------
% 0.22/0.48  % (18020)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (18020)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f409,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f72,f82,f104,f133,f178,f249,f273,f310,f391,f398,f407])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    spl3_3 | ~spl3_28),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f402])).
% 0.22/0.49  fof(f402,plain,(
% 0.22/0.49    $false | (spl3_3 | ~spl3_28)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f81,f35,f397,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl3_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f396])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    spl3_28 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl3_3 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f398,plain,(
% 0.22/0.49    spl3_28 | ~spl3_1 | ~spl3_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f394,f388,f69,f396])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl3_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    spl3_27 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl3_1 | ~spl3_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f392,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f392,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0))) ) | ~spl3_27),
% 0.22/0.49    inference(resolution,[],[f390,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | ~spl3_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f388])).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    spl3_27 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f385,f131,f388])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl3_9 <=> ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | ~spl3_9),
% 0.22/0.49    inference(resolution,[],[f85,f132])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f131])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(X5,k1_zfmisc_1(k2_tarski(k4_tarski(X6,X7),k4_tarski(X8,X9)))) | v1_relat_1(X5)) )),
% 0.22/0.49    inference(resolution,[],[f58,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.22/0.49  fof(f310,plain,(
% 0.22/0.49    spl3_3 | ~spl3_18),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    $false | (spl3_3 | ~spl3_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f81,f272])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    ( ! [X0,X1] : (X0 = X1) ) | ~spl3_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f271])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    spl3_18 <=> ! [X1,X0] : X0 = X1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    spl3_18 | ~spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f260,f247,f271])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    spl3_14 <=> ! [X0] : k1_xboole_0 = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    ( ! [X0,X1] : (X0 = X1) ) | ~spl3_14),
% 0.22/0.49    inference(superposition,[],[f248,f248])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f247])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    spl3_14 | ~spl3_5 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f227,f176,f101,f247])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl3_5 <=> k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl3_11 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0) ) | (~spl3_5 | ~spl3_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f137,f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0)) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.22/0.49    inference(superposition,[],[f42,f103])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f101])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    spl3_11 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f174,f101,f176])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_5),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_5),
% 0.22/0.49    inference(superposition,[],[f129,f103])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k3_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | k3_xboole_0(X0,X1) = k1_tarski(X2) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.49    inference(superposition,[],[f67,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl3_9 | ~spl3_4 | spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f101,f98,f131])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl3_4 <=> ! [X0] : k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | (~spl3_4 | spl3_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f127,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | (~spl3_4 | spl3_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f126,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    k1_xboole_0 != k1_tarski(k1_xboole_0) | spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f101])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(k1_xboole_0) | ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl3_4),
% 0.22/0.49    inference(superposition,[],[f40,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0))) ) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl3_4 | spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f101,f98])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k1_tarski(k1_xboole_0) | k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0))) )),
% 0.22/0.49    inference(resolution,[],[f90,f36])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(X0) | sK1(X1,k1_tarski(X0)) = X0) )),
% 0.22/0.49    inference(resolution,[],[f41,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.49    inference(equality_resolution,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.49    inference(rectify,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f79])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f69])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18020)------------------------------
% 0.22/0.49  % (18020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18020)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18020)Memory used [KB]: 6268
% 0.22/0.49  % (18020)Time elapsed: 0.075 s
% 0.22/0.49  % (18020)------------------------------
% 0.22/0.49  % (18020)------------------------------
% 0.22/0.49  % (18017)Success in time 0.128 s
%------------------------------------------------------------------------------
