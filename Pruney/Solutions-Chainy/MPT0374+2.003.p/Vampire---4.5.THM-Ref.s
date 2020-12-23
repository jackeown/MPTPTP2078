%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 192 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  386 ( 699 expanded)
%              Number of equality atoms :   66 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f333,f418,f501,f510,f517,f523])).

fof(f523,plain,
    ( spl6_13
    | spl6_2
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f522,f311,f116,f106,f186])).

fof(f186,plain,
    ( spl6_13
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f106,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f116,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f311,plain,
    ( spl6_15
  <=> ! [X2,X4] :
        ( r2_hidden(X4,X2)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f522,plain,
    ( r2_hidden(sK1,sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f340,f108])).

fof(f108,plain,
    ( k1_xboole_0 != sK0
    | spl6_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f340,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0)
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(resolution,[],[f312,f118])).

fof(f118,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f312,plain,
    ( ! [X4,X2] :
        ( ~ m1_subset_1(X4,X2)
        | k1_xboole_0 = X2
        | r2_hidden(X4,X2) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f311])).

fof(f517,plain,
    ( spl6_12
    | spl6_2
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f516,f311,f111,f106,f180])).

fof(f180,plain,
    ( spl6_12
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f111,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f516,plain,
    ( r2_hidden(sK2,sK0)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f339,f108])).

fof(f339,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2,sK0)
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(resolution,[],[f312,f113])).

fof(f113,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f510,plain,(
    ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f170,f161,f231])).

fof(f231,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f226,f92])).

fof(f92,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f223,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f223,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f220,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f95,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f60,f120])).

fof(f120,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f161,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_11
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f170,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f80,f79])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f501,plain,
    ( ~ spl6_16
    | spl6_11
    | spl6_1 ),
    inference(avatar_split_clause,[],[f495,f101,f160,f325])).

fof(f325,plain,
    ( spl6_16
  <=> r1_tarski(k2_tarski(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f101,plain,
    ( spl6_1
  <=> m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f495,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ r1_tarski(k2_tarski(sK1,sK2),sK0)
    | spl6_1 ),
    inference(resolution,[],[f193,f103])).

fof(f103,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f193,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(k1_zfmisc_1(X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f85,f92])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f418,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_13
    | spl6_16 ),
    inference(subsumption_resolution,[],[f416,f188])).

fof(f188,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f416,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl6_12
    | spl6_16 ),
    inference(subsumption_resolution,[],[f411,f182])).

fof(f182,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f411,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0)
    | spl6_16 ),
    inference(resolution,[],[f255,f327])).

fof(f327,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK2),sK0)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f325])).

fof(f255,plain,(
    ! [X23,X21,X22] :
      ( r1_tarski(k2_tarski(X21,X22),X23)
      | ~ r2_hidden(X22,X23)
      | ~ r2_hidden(X21,X23) ) ),
    inference(trivial_inequality_removal,[],[f254])).

fof(f254,plain,(
    ! [X23,X21,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k2_tarski(X21,X22),X23)
      | ~ r2_hidden(X22,X23)
      | ~ r2_hidden(X21,X23) ) ),
    inference(superposition,[],[f80,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f333,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f304,f311])).

fof(f304,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f303,f120])).

fof(f303,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f301,f223])).

fof(f301,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X1,k1_xboole_0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f62,f165])).

fof(f165,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f164,f91])).

fof(f91,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f164,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f89,f83])).

fof(f89,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f119,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f52,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X2,sK0) )
   => ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(f114,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f53,f111])).

fof(f53,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:05:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (2439)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (2441)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (2440)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (2442)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (2437)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (2443)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (2460)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (2447)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (2452)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (2453)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (2456)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (2447)Refutation not found, incomplete strategy% (2447)------------------------------
% 0.21/0.55  % (2447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2454)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (2447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2447)Memory used [KB]: 10746
% 0.21/0.55  % (2447)Time elapsed: 0.113 s
% 0.21/0.55  % (2447)------------------------------
% 0.21/0.55  % (2447)------------------------------
% 0.21/0.55  % (2457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (2455)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (2445)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (2455)Refutation not found, incomplete strategy% (2455)------------------------------
% 0.21/0.55  % (2455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2455)Memory used [KB]: 1663
% 0.21/0.55  % (2455)Time elapsed: 0.136 s
% 0.21/0.55  % (2455)------------------------------
% 0.21/0.55  % (2455)------------------------------
% 0.21/0.55  % (2465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (2450)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (2461)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (2438)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (2438)Refutation not found, incomplete strategy% (2438)------------------------------
% 0.21/0.55  % (2438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2438)Memory used [KB]: 1663
% 0.21/0.55  % (2438)Time elapsed: 0.130 s
% 0.21/0.55  % (2438)------------------------------
% 0.21/0.55  % (2438)------------------------------
% 0.21/0.55  % (2465)Refutation not found, incomplete strategy% (2465)------------------------------
% 0.21/0.55  % (2465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2465)Memory used [KB]: 10746
% 0.21/0.55  % (2465)Time elapsed: 0.133 s
% 0.21/0.55  % (2465)------------------------------
% 0.21/0.55  % (2465)------------------------------
% 0.21/0.55  % (2458)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (2448)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (2449)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (2459)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (2446)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (2449)Refutation not found, incomplete strategy% (2449)------------------------------
% 0.21/0.56  % (2449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2449)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2449)Memory used [KB]: 10618
% 0.21/0.56  % (2449)Time elapsed: 0.146 s
% 0.21/0.56  % (2449)------------------------------
% 0.21/0.56  % (2449)------------------------------
% 0.21/0.56  % (2464)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (2444)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (2464)Refutation not found, incomplete strategy% (2464)------------------------------
% 0.21/0.56  % (2464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2464)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2464)Memory used [KB]: 6140
% 0.21/0.56  % (2464)Time elapsed: 0.147 s
% 0.21/0.56  % (2464)------------------------------
% 0.21/0.56  % (2464)------------------------------
% 0.21/0.56  % (2453)Refutation not found, incomplete strategy% (2453)------------------------------
% 0.21/0.56  % (2453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2453)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2453)Memory used [KB]: 10746
% 0.21/0.56  % (2453)Time elapsed: 0.146 s
% 0.21/0.56  % (2453)------------------------------
% 0.21/0.56  % (2453)------------------------------
% 0.21/0.56  % (2451)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (2462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (2463)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (2466)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (2466)Refutation not found, incomplete strategy% (2466)------------------------------
% 0.21/0.57  % (2466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (2466)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (2466)Memory used [KB]: 1663
% 0.21/0.57  % (2466)Time elapsed: 0.002 s
% 0.21/0.57  % (2466)------------------------------
% 0.21/0.57  % (2466)------------------------------
% 0.21/0.58  % (2458)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f524,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f333,f418,f501,f510,f517,f523])).
% 0.21/0.58  fof(f523,plain,(
% 0.21/0.58    spl6_13 | spl6_2 | ~spl6_4 | ~spl6_15),
% 0.21/0.58    inference(avatar_split_clause,[],[f522,f311,f116,f106,f186])).
% 0.21/0.58  fof(f186,plain,(
% 0.21/0.58    spl6_13 <=> r2_hidden(sK1,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    spl6_2 <=> k1_xboole_0 = sK0),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    spl6_4 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.58  fof(f311,plain,(
% 0.21/0.58    spl6_15 <=> ! [X2,X4] : (r2_hidden(X4,X2) | k1_xboole_0 = X2 | ~m1_subset_1(X4,X2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.58  fof(f522,plain,(
% 0.21/0.58    r2_hidden(sK1,sK0) | (spl6_2 | ~spl6_4 | ~spl6_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f340,f108])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    k1_xboole_0 != sK0 | spl6_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f106])).
% 0.21/0.58  fof(f340,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0) | (~spl6_4 | ~spl6_15)),
% 0.21/0.58    inference(resolution,[],[f312,f118])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    m1_subset_1(sK1,sK0) | ~spl6_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f116])).
% 0.21/0.58  fof(f312,plain,(
% 0.21/0.58    ( ! [X4,X2] : (~m1_subset_1(X4,X2) | k1_xboole_0 = X2 | r2_hidden(X4,X2)) ) | ~spl6_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f311])).
% 0.21/0.58  fof(f517,plain,(
% 0.21/0.58    spl6_12 | spl6_2 | ~spl6_3 | ~spl6_15),
% 0.21/0.58    inference(avatar_split_clause,[],[f516,f311,f111,f106,f180])).
% 0.21/0.58  fof(f180,plain,(
% 0.21/0.58    spl6_12 <=> r2_hidden(sK2,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    spl6_3 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.58  fof(f516,plain,(
% 0.21/0.58    r2_hidden(sK2,sK0) | (spl6_2 | ~spl6_3 | ~spl6_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f339,f108])).
% 0.21/0.58  fof(f339,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | r2_hidden(sK2,sK0) | (~spl6_3 | ~spl6_15)),
% 0.21/0.58    inference(resolution,[],[f312,f113])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    m1_subset_1(sK2,sK0) | ~spl6_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f111])).
% 0.21/0.58  fof(f510,plain,(
% 0.21/0.58    ~spl6_11),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f502])).
% 0.21/0.58  fof(f502,plain,(
% 0.21/0.58    $false | ~spl6_11),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f170,f161,f231])).
% 0.21/0.58  fof(f231,plain,(
% 0.21/0.58    ( ! [X4,X3] : (~r1_tarski(X4,X3) | ~v1_xboole_0(k1_zfmisc_1(X3))) )),
% 0.21/0.58    inference(resolution,[],[f226,f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.58    inference(rectify,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.58  fof(f226,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(superposition,[],[f223,f82])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f220,f197])).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.58    inference(superposition,[],[f95,f79])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(rectify,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(flattening,[],[f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.58  fof(f220,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(resolution,[],[f60,f120])).
% 0.21/0.58  fof(f120,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f63,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f160])).
% 0.21/0.58  fof(f160,plain,(
% 0.21/0.58    spl6_11 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.58  fof(f170,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f169])).
% 0.21/0.58  fof(f169,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(superposition,[],[f80,f79])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.58    inference(nnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.58  fof(f501,plain,(
% 0.21/0.58    ~spl6_16 | spl6_11 | spl6_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f495,f101,f160,f325])).
% 0.21/0.58  fof(f325,plain,(
% 0.21/0.58    spl6_16 <=> r1_tarski(k2_tarski(sK1,sK2),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    spl6_1 <=> m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.58  fof(f495,plain,(
% 0.21/0.58    v1_xboole_0(k1_zfmisc_1(sK0)) | ~r1_tarski(k2_tarski(sK1,sK2),sK0) | spl6_1),
% 0.21/0.58    inference(resolution,[],[f193,f103])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) | spl6_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f101])).
% 0.21/0.58  fof(f193,plain,(
% 0.21/0.58    ( ! [X2,X1] : (m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(k1_zfmisc_1(X2)) | ~r1_tarski(X1,X2)) )),
% 0.21/0.58    inference(resolution,[],[f85,f92])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.58  fof(f418,plain,(
% 0.21/0.58    ~spl6_12 | ~spl6_13 | spl6_16),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f417])).
% 0.21/0.58  fof(f417,plain,(
% 0.21/0.58    $false | (~spl6_12 | ~spl6_13 | spl6_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f416,f188])).
% 0.21/0.58  fof(f188,plain,(
% 0.21/0.58    r2_hidden(sK1,sK0) | ~spl6_13),
% 0.21/0.58    inference(avatar_component_clause,[],[f186])).
% 0.21/0.58  fof(f416,plain,(
% 0.21/0.58    ~r2_hidden(sK1,sK0) | (~spl6_12 | spl6_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f411,f182])).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    r2_hidden(sK2,sK0) | ~spl6_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f180])).
% 0.21/0.58  fof(f411,plain,(
% 0.21/0.58    ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0) | spl6_16),
% 0.21/0.58    inference(resolution,[],[f255,f327])).
% 0.21/0.58  fof(f327,plain,(
% 0.21/0.58    ~r1_tarski(k2_tarski(sK1,sK2),sK0) | spl6_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f325])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    ( ! [X23,X21,X22] : (r1_tarski(k2_tarski(X21,X22),X23) | ~r2_hidden(X22,X23) | ~r2_hidden(X21,X23)) )),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f254])).
% 0.21/0.58  fof(f254,plain,(
% 0.21/0.58    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_tarski(X21,X22),X23) | ~r2_hidden(X22,X23) | ~r2_hidden(X21,X23)) )),
% 0.21/0.58    inference(superposition,[],[f80,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.58    inference(flattening,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.58    inference(nnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.21/0.58  fof(f333,plain,(
% 0.21/0.58    spl6_15),
% 0.21/0.58    inference(avatar_split_clause,[],[f304,f311])).
% 0.21/0.58  fof(f304,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f303,f120])).
% 0.21/0.58  fof(f303,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f301,f223])).
% 0.21/0.58  fof(f301,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X1,k1_xboole_0) | ~m1_subset_1(X1,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(superposition,[],[f62,f165])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(forward_demodulation,[],[f164,f91])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f89,f83])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.21/0.58    inference(flattening,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    spl6_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f52,f116])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    m1_subset_1(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f32,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) => (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.21/0.58    inference(flattening,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f19])).
% 0.21/0.58  fof(f19,conjecture,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    spl6_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f53,f111])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    m1_subset_1(sK2,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    ~spl6_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f54,f106])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    k1_xboole_0 != sK0),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ~spl6_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f55,f101])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (2458)------------------------------
% 0.21/0.58  % (2458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (2458)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (2458)Memory used [KB]: 6524
% 0.21/0.58  % (2458)Time elapsed: 0.152 s
% 0.21/0.58  % (2458)------------------------------
% 0.21/0.58  % (2458)------------------------------
% 0.21/0.58  % (2436)Success in time 0.215 s
%------------------------------------------------------------------------------
