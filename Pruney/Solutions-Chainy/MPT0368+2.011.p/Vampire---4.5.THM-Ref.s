%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 200 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  310 ( 829 expanded)
%              Number of equality atoms :   36 ( 120 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f113,f149,f188,f194,f208,f209,f233,f263])).

fof(f263,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( sK0 != sK0
    | ~ spl5_4 ),
    inference(superposition,[],[f35,f108])).

fof(f108,plain,
    ( sK0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f35,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK0 != sK1
      & ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f233,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl5_7 ),
    inference(resolution,[],[f144,f36])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f144,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f209,plain,
    ( ~ spl5_3
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl5_3
    | spl5_12 ),
    inference(resolution,[],[f195,f104])).

fof(f104,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f195,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_12 ),
    inference(resolution,[],[f193,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f193,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_12
  <=> r2_hidden(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f208,plain,
    ( ~ spl5_1
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl5_1
    | spl5_12 ),
    inference(resolution,[],[f195,f176])).

fof(f176,plain,
    ( ! [X3] : r1_tarski(sK0,X3)
    | ~ spl5_1 ),
    inference(resolution,[],[f172,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f172,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f61,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f194,plain,
    ( ~ spl5_12
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f189,f110,f106,f191])).

fof(f110,plain,
    ( spl5_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f189,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,k1_zfmisc_1(sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f111,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f72,plain,(
    ! [X4,X5,X3] :
      ( r2_xboole_0(X3,X5)
      | X3 = X4
      | ~ r2_hidden(X4,k1_zfmisc_1(X5))
      | ~ r2_hidden(X3,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | X3 = X5
      | r2_xboole_0(X3,X4)
      | ~ r2_hidden(X5,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f68,f56])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_xboole_0(X2,X1)
      | X0 = X2
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f111,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f188,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f148,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f149,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_5 ),
    inference(avatar_split_clause,[],[f140,f110,f146,f142])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl5_5 ),
    inference(resolution,[],[f112,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f112,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f98,f63,f110,f106,f102])).

fof(f63,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f98,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | sK0 = sK1
    | r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f97,f44])).

fof(f97,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK3(X8,sK1),sK0)
        | ~ r2_hidden(sK1,k1_zfmisc_1(X8))
        | sK1 = X8 )
    | ~ spl5_2 ),
    inference(resolution,[],[f91,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X1,X0),X0)
      | X0 = X1
      | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f85,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f82,f55])).

fof(f65,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f57,f63,f59])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.52  % (22743)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (22745)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (22737)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.53  % (22743)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f264,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(avatar_sat_refutation,[],[f65,f113,f149,f188,f194,f208,f209,f233,f263])).
% 0.19/0.53  fof(f263,plain,(
% 0.19/0.53    ~spl5_4),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f262])).
% 0.19/0.53  fof(f262,plain,(
% 0.19/0.53    $false | ~spl5_4),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f261])).
% 0.19/0.53  fof(f261,plain,(
% 0.19/0.53    sK0 != sK0 | ~spl5_4),
% 0.19/0.53    inference(superposition,[],[f35,f108])).
% 0.19/0.53  fof(f108,plain,(
% 0.19/0.53    sK0 = sK1 | ~spl5_4),
% 0.19/0.53    inference(avatar_component_clause,[],[f106])).
% 0.19/0.53  fof(f106,plain,(
% 0.19/0.53    spl5_4 <=> sK0 = sK1),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    sK0 != sK1),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f11,plain,(
% 0.19/0.53    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(flattening,[],[f10])).
% 0.19/0.53  fof(f10,plain,(
% 0.19/0.53    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.19/0.53    inference(negated_conjecture,[],[f8])).
% 0.19/0.53  fof(f8,conjecture,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.19/0.53  fof(f233,plain,(
% 0.19/0.53    ~spl5_7),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f229])).
% 0.19/0.53  fof(f229,plain,(
% 0.19/0.53    $false | ~spl5_7),
% 0.19/0.53    inference(resolution,[],[f144,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.53  fof(f144,plain,(
% 0.19/0.53    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_7),
% 0.19/0.53    inference(avatar_component_clause,[],[f142])).
% 0.19/0.53  fof(f142,plain,(
% 0.19/0.53    spl5_7 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.53  fof(f209,plain,(
% 0.19/0.53    ~spl5_3 | spl5_12),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f204])).
% 0.19/0.53  fof(f204,plain,(
% 0.19/0.53    $false | (~spl5_3 | spl5_12)),
% 0.19/0.53    inference(resolution,[],[f195,f104])).
% 0.19/0.53  fof(f104,plain,(
% 0.19/0.53    r1_tarski(sK0,sK1) | ~spl5_3),
% 0.19/0.53    inference(avatar_component_clause,[],[f102])).
% 0.19/0.53  fof(f102,plain,(
% 0.19/0.53    spl5_3 <=> r1_tarski(sK0,sK1)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.53  fof(f195,plain,(
% 0.19/0.53    ~r1_tarski(sK0,sK1) | spl5_12),
% 0.19/0.53    inference(resolution,[],[f193,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f50])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f32])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.53    inference(rectify,[],[f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.53  fof(f193,plain,(
% 0.19/0.53    ~r2_hidden(sK0,k1_zfmisc_1(sK1)) | spl5_12),
% 0.19/0.53    inference(avatar_component_clause,[],[f191])).
% 0.19/0.53  fof(f191,plain,(
% 0.19/0.53    spl5_12 <=> r2_hidden(sK0,k1_zfmisc_1(sK1))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.53  fof(f208,plain,(
% 0.19/0.53    ~spl5_1 | spl5_12),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f205])).
% 0.19/0.53  fof(f205,plain,(
% 0.19/0.53    $false | (~spl5_1 | spl5_12)),
% 0.19/0.53    inference(resolution,[],[f195,f176])).
% 0.19/0.53  fof(f176,plain,(
% 0.19/0.53    ( ! [X3] : (r1_tarski(sK0,X3)) ) | ~spl5_1),
% 0.19/0.53    inference(resolution,[],[f172,f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f26])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(rectify,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(nnf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,plain,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.53  fof(f172,plain,(
% 0.19/0.53    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl5_1),
% 0.19/0.53    inference(resolution,[],[f61,f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.53    inference(rectify,[],[f18])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.53    inference(nnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    v1_xboole_0(sK0) | ~spl5_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f59])).
% 0.19/0.53  fof(f59,plain,(
% 0.19/0.53    spl5_1 <=> v1_xboole_0(sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.53  fof(f194,plain,(
% 0.19/0.53    ~spl5_12 | spl5_4 | ~spl5_5),
% 0.19/0.53    inference(avatar_split_clause,[],[f189,f110,f106,f191])).
% 0.19/0.53  fof(f110,plain,(
% 0.19/0.53    spl5_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.53  fof(f189,plain,(
% 0.19/0.53    sK0 = sK1 | ~r2_hidden(sK0,k1_zfmisc_1(sK1)) | ~spl5_5),
% 0.19/0.53    inference(resolution,[],[f111,f82])).
% 0.19/0.53  fof(f82,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | X0 = X1 | ~r2_hidden(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.53    inference(resolution,[],[f72,f54])).
% 0.19/0.53  fof(f54,plain,(
% 0.19/0.53    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.19/0.53    inference(equality_resolution,[],[f47])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.53    inference(flattening,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.53    inference(nnf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    ( ! [X4,X5,X3] : (r2_xboole_0(X3,X5) | X3 = X4 | ~r2_hidden(X4,k1_zfmisc_1(X5)) | ~r2_hidden(X3,k1_zfmisc_1(X4))) )),
% 0.19/0.53    inference(resolution,[],[f70,f56])).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(equality_resolution,[],[f49])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f32])).
% 0.19/0.53  fof(f70,plain,(
% 0.19/0.53    ( ! [X4,X5,X3] : (~r1_tarski(X3,X5) | X3 = X5 | r2_xboole_0(X3,X4) | ~r2_hidden(X5,k1_zfmisc_1(X4))) )),
% 0.19/0.53    inference(resolution,[],[f68,f56])).
% 0.19/0.53  fof(f68,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_xboole_0(X2,X1) | X0 = X2 | ~r1_tarski(X2,X0)) )),
% 0.19/0.53    inference(resolution,[],[f53,f48])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f28])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r2_xboole_0(X0,X1) | ~r1_tarski(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.19/0.53    inference(flattening,[],[f14])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.19/0.53  fof(f111,plain,(
% 0.19/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.19/0.53    inference(avatar_component_clause,[],[f110])).
% 0.19/0.53  fof(f188,plain,(
% 0.19/0.53    spl5_8),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f186])).
% 0.19/0.53  fof(f186,plain,(
% 0.19/0.53    $false | spl5_8),
% 0.19/0.53    inference(resolution,[],[f148,f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f148,plain,(
% 0.19/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_8),
% 0.19/0.53    inference(avatar_component_clause,[],[f146])).
% 0.19/0.53  fof(f146,plain,(
% 0.19/0.53    spl5_8 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.53  fof(f149,plain,(
% 0.19/0.53    spl5_7 | ~spl5_8 | spl5_5),
% 0.19/0.53    inference(avatar_split_clause,[],[f140,f110,f146,f142])).
% 0.19/0.53  fof(f140,plain,(
% 0.19/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl5_5),
% 0.19/0.53    inference(resolution,[],[f112,f39])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.53    inference(nnf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,plain,(
% 0.19/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.53  fof(f112,plain,(
% 0.19/0.53    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl5_5),
% 0.19/0.53    inference(avatar_component_clause,[],[f110])).
% 0.19/0.53  fof(f113,plain,(
% 0.19/0.53    spl5_3 | spl5_4 | ~spl5_5 | ~spl5_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f98,f63,f110,f106,f102])).
% 0.19/0.53  fof(f63,plain,(
% 0.19/0.53    spl5_2 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.53  fof(f98,plain,(
% 0.19/0.53    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | sK0 = sK1 | r1_tarski(sK0,sK1) | ~spl5_2),
% 0.19/0.53    inference(resolution,[],[f97,f44])).
% 0.19/0.53  fof(f97,plain,(
% 0.19/0.53    ( ! [X8] : (~r2_hidden(sK3(X8,sK1),sK0) | ~r2_hidden(sK1,k1_zfmisc_1(X8)) | sK1 = X8) ) | ~spl5_2),
% 0.19/0.53    inference(resolution,[],[f91,f64])).
% 0.19/0.53  fof(f64,plain,(
% 0.19/0.53    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f63])).
% 0.19/0.53  fof(f91,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X1,X0),X0) | X0 = X1 | ~r2_hidden(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.53    inference(resolution,[],[f85,f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f26])).
% 0.19/0.53  fof(f85,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,k1_zfmisc_1(X1)) | X0 = X1) )),
% 0.19/0.53    inference(resolution,[],[f82,f55])).
% 0.19/0.53  fof(f65,plain,(
% 0.19/0.53    spl5_1 | spl5_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f57,f63,f59])).
% 0.19/0.53  fof(f57,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_xboole_0(sK0) | r2_hidden(X0,sK1)) )),
% 0.19/0.53    inference(resolution,[],[f40,f34])).
% 0.19/0.53  fof(f34,plain,(
% 0.19/0.53    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (22743)------------------------------
% 0.19/0.53  % (22743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (22743)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (22743)Memory used [KB]: 6268
% 0.19/0.53  % (22743)Time elapsed: 0.111 s
% 0.19/0.53  % (22743)------------------------------
% 0.19/0.53  % (22743)------------------------------
% 0.19/0.53  % (22730)Success in time 0.176 s
%------------------------------------------------------------------------------
