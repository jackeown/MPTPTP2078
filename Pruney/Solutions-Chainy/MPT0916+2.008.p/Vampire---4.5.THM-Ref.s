%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:38 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 281 expanded)
%              Number of leaves         :   21 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 ( 874 expanded)
%              Number of equality atoms :   56 ( 113 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f283,f285,f289,f303,f317,f332,f387,f391,f412,f416])).

fof(f416,plain,(
    spl9_25 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl9_25 ),
    inference(subsumption_resolution,[],[f181,f411])).

fof(f411,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl9_25 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl9_25
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f181,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    inference(resolution,[],[f180,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f180,plain,(
    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f412,plain,
    ( spl9_18
    | ~ spl9_19
    | spl9_20
    | spl9_21
    | ~ spl9_25
    | spl9_3 ),
    inference(avatar_split_clause,[],[f407,f71,f409,f276,f272,f268,f264])).

fof(f264,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f268,plain,
    ( spl9_19
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f272,plain,
    ( spl9_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f276,plain,
    ( spl9_21
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f71,plain,
    ( spl9_3
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f407,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl9_3 ),
    inference(superposition,[],[f73,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f73,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f391,plain,(
    spl9_24 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | spl9_24 ),
    inference(subsumption_resolution,[],[f237,f386])).

fof(f386,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | spl9_24 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl9_24
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f237,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    inference(resolution,[],[f51,f180])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f387,plain,
    ( spl9_18
    | ~ spl9_19
    | spl9_20
    | spl9_21
    | ~ spl9_24
    | spl9_2 ),
    inference(avatar_split_clause,[],[f382,f67,f384,f276,f272,f268,f264])).

fof(f67,plain,
    ( spl9_2
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f382,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl9_2 ),
    inference(superposition,[],[f69,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f332,plain,(
    ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f239,f108,f321,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f81,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f321,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl9_21 ),
    inference(superposition,[],[f79,f278])).

fof(f278,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f276])).

fof(f79,plain,(
    r1_tarski(sK4,sK1) ),
    inference(resolution,[],[f44,f29])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f102,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f102,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f239,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f237,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f317,plain,(
    ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f238,f108,f306,f82])).

fof(f306,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl9_20 ),
    inference(superposition,[],[f80,f274])).

fof(f274,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f272])).

fof(f80,plain,(
    r1_tarski(sK5,sK2) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f238,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(resolution,[],[f236,f33])).

fof(f236,plain,(
    r2_hidden(k2_mcart_1(sK6),sK5) ),
    inference(resolution,[],[f51,f55])).

fof(f303,plain,(
    ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f183,f108,f292,f82])).

fof(f292,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_18 ),
    inference(superposition,[],[f78,f266])).

fof(f266,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f264])).

fof(f78,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f183,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f181,f33])).

fof(f289,plain,(
    spl9_22 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl9_22 ),
    inference(subsumption_resolution,[],[f236,f282])).

fof(f282,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl9_22
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f285,plain,(
    spl9_19 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl9_19 ),
    inference(subsumption_resolution,[],[f56,f270])).

fof(f270,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f268])).

fof(f56,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f26,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f283,plain,
    ( spl9_18
    | ~ spl9_19
    | spl9_20
    | spl9_21
    | ~ spl9_22
    | spl9_1 ),
    inference(avatar_split_clause,[],[f262,f63,f280,f276,f272,f268,f264])).

fof(f63,plain,
    ( spl9_1
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f262,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl9_1 ),
    inference(superposition,[],[f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f47])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f74,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f25,f71,f67,f63])).

fof(f25,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:43:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (11062)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (11075)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (11080)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (11070)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (11067)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.53  % (11085)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.53  % (11077)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.53  % (11075)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f417,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f74,f283,f285,f289,f303,f317,f332,f387,f391,f412,f416])).
% 1.26/0.53  fof(f416,plain,(
% 1.26/0.53    spl9_25),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f413])).
% 1.26/0.53  fof(f413,plain,(
% 1.26/0.53    $false | spl9_25),
% 1.26/0.53    inference(subsumption_resolution,[],[f181,f411])).
% 1.26/0.53  fof(f411,plain,(
% 1.26/0.53    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | spl9_25),
% 1.26/0.53    inference(avatar_component_clause,[],[f409])).
% 1.26/0.53  fof(f409,plain,(
% 1.26/0.53    spl9_25 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.26/0.53  fof(f181,plain,(
% 1.26/0.53    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.26/0.53    inference(resolution,[],[f180,f50])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f23])).
% 1.26/0.53  fof(f23,plain,(
% 1.26/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.26/0.53    inference(ennf_transformation,[],[f12])).
% 1.26/0.53  fof(f12,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.26/0.53  fof(f180,plain,(
% 1.26/0.53    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 1.26/0.53    inference(resolution,[],[f50,f55])).
% 1.26/0.53  fof(f55,plain,(
% 1.26/0.53    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.26/0.53    inference(definition_unfolding,[],[f27,f47])).
% 1.26/0.53  fof(f47,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f11])).
% 1.26/0.53  fof(f11,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.26/0.53    inference(cnf_transformation,[],[f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.26/0.53    inference(flattening,[],[f17])).
% 1.26/0.53  fof(f17,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f15])).
% 1.26/0.53  fof(f15,negated_conjecture,(
% 1.26/0.53    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.26/0.53    inference(negated_conjecture,[],[f14])).
% 1.26/0.54  fof(f14,conjecture,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 1.26/0.54  fof(f412,plain,(
% 1.26/0.54    spl9_18 | ~spl9_19 | spl9_20 | spl9_21 | ~spl9_25 | spl9_3),
% 1.26/0.54    inference(avatar_split_clause,[],[f407,f71,f409,f276,f272,f268,f264])).
% 1.26/0.54  fof(f264,plain,(
% 1.26/0.54    spl9_18 <=> k1_xboole_0 = sK0),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.26/0.54  fof(f268,plain,(
% 1.26/0.54    spl9_19 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.26/0.54  fof(f272,plain,(
% 1.26/0.54    spl9_20 <=> k1_xboole_0 = sK2),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.26/0.54  fof(f276,plain,(
% 1.26/0.54    spl9_21 <=> k1_xboole_0 = sK1),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.26/0.54  fof(f71,plain,(
% 1.26/0.54    spl9_3 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.26/0.54  fof(f407,plain,(
% 1.26/0.54    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl9_3),
% 1.26/0.54    inference(superposition,[],[f73,f59])).
% 1.26/0.54  fof(f59,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(definition_unfolding,[],[f52,f47])).
% 1.26/0.54  fof(f52,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f24])).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.54    inference(ennf_transformation,[],[f13])).
% 1.26/0.54  fof(f13,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.26/0.54  fof(f73,plain,(
% 1.26/0.54    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl9_3),
% 1.26/0.54    inference(avatar_component_clause,[],[f71])).
% 1.26/0.54  fof(f391,plain,(
% 1.26/0.54    spl9_24),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f388])).
% 1.26/0.54  fof(f388,plain,(
% 1.26/0.54    $false | spl9_24),
% 1.26/0.54    inference(subsumption_resolution,[],[f237,f386])).
% 1.26/0.54  fof(f386,plain,(
% 1.26/0.54    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | spl9_24),
% 1.26/0.54    inference(avatar_component_clause,[],[f384])).
% 1.26/0.54  fof(f384,plain,(
% 1.26/0.54    spl9_24 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.26/0.54  fof(f237,plain,(
% 1.26/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 1.26/0.54    inference(resolution,[],[f51,f180])).
% 1.26/0.54  fof(f51,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f23])).
% 1.26/0.54  fof(f387,plain,(
% 1.26/0.54    spl9_18 | ~spl9_19 | spl9_20 | spl9_21 | ~spl9_24 | spl9_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f382,f67,f384,f276,f272,f268,f264])).
% 1.26/0.54  fof(f67,plain,(
% 1.26/0.54    spl9_2 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.26/0.54  fof(f382,plain,(
% 1.26/0.54    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl9_2),
% 1.26/0.54    inference(superposition,[],[f69,f58])).
% 1.26/0.54  fof(f58,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(definition_unfolding,[],[f53,f47])).
% 1.26/0.54  fof(f53,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f24])).
% 1.26/0.54  fof(f69,plain,(
% 1.26/0.54    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl9_2),
% 1.26/0.54    inference(avatar_component_clause,[],[f67])).
% 1.26/0.54  fof(f332,plain,(
% 1.26/0.54    ~spl9_21),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f325])).
% 1.26/0.54  fof(f325,plain,(
% 1.26/0.54    $false | ~spl9_21),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f239,f108,f321,f82])).
% 1.26/0.54  fof(f82,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(superposition,[],[f81,f36])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f20])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f7])).
% 1.26/0.54  fof(f7,axiom,(
% 1.26/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.26/0.54  fof(f81,plain,(
% 1.26/0.54    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.26/0.54    inference(resolution,[],[f34,f32])).
% 1.26/0.54  fof(f32,plain,(
% 1.26/0.54    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f1])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.26/0.54  fof(f34,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f19])).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.26/0.54    inference(ennf_transformation,[],[f16])).
% 1.26/0.54  fof(f16,plain,(
% 1.26/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.26/0.54    inference(rectify,[],[f3])).
% 1.26/0.54  fof(f3,axiom,(
% 1.26/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.26/0.54  fof(f321,plain,(
% 1.26/0.54    r1_tarski(sK4,k1_xboole_0) | ~spl9_21),
% 1.26/0.54    inference(superposition,[],[f79,f278])).
% 1.26/0.54  fof(f278,plain,(
% 1.26/0.54    k1_xboole_0 = sK1 | ~spl9_21),
% 1.26/0.54    inference(avatar_component_clause,[],[f276])).
% 1.26/0.54  fof(f79,plain,(
% 1.26/0.54    r1_tarski(sK4,sK1)),
% 1.26/0.54    inference(resolution,[],[f44,f29])).
% 1.26/0.54  fof(f29,plain,(
% 1.26/0.54    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f10])).
% 1.26/0.54  fof(f10,axiom,(
% 1.26/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.26/0.54  fof(f108,plain,(
% 1.26/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.26/0.54    inference(resolution,[],[f102,f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f21])).
% 1.26/0.54  fof(f21,plain,(
% 1.26/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f2])).
% 1.26/0.54  fof(f2,axiom,(
% 1.26/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.26/0.54  fof(f102,plain,(
% 1.26/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.26/0.54    inference(resolution,[],[f49,f31])).
% 1.26/0.54  fof(f31,plain,(
% 1.26/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f8])).
% 1.26/0.54  fof(f8,axiom,(
% 1.26/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.26/0.54  fof(f49,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f22])).
% 1.26/0.54  fof(f22,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.26/0.54    inference(ennf_transformation,[],[f6])).
% 1.26/0.54  fof(f6,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.26/0.54  fof(f239,plain,(
% 1.26/0.54    ~v1_xboole_0(sK4)),
% 1.26/0.54    inference(resolution,[],[f237,f33])).
% 1.26/0.54  fof(f33,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f1])).
% 1.26/0.54  fof(f317,plain,(
% 1.26/0.54    ~spl9_20),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f310])).
% 1.26/0.54  fof(f310,plain,(
% 1.26/0.54    $false | ~spl9_20),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f238,f108,f306,f82])).
% 1.26/0.54  fof(f306,plain,(
% 1.26/0.54    r1_tarski(sK5,k1_xboole_0) | ~spl9_20),
% 1.26/0.54    inference(superposition,[],[f80,f274])).
% 1.26/0.54  fof(f274,plain,(
% 1.26/0.54    k1_xboole_0 = sK2 | ~spl9_20),
% 1.26/0.54    inference(avatar_component_clause,[],[f272])).
% 1.26/0.54  fof(f80,plain,(
% 1.26/0.54    r1_tarski(sK5,sK2)),
% 1.26/0.54    inference(resolution,[],[f44,f28])).
% 1.26/0.54  fof(f28,plain,(
% 1.26/0.54    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  fof(f238,plain,(
% 1.26/0.54    ~v1_xboole_0(sK5)),
% 1.26/0.54    inference(resolution,[],[f236,f33])).
% 1.26/0.54  fof(f236,plain,(
% 1.26/0.54    r2_hidden(k2_mcart_1(sK6),sK5)),
% 1.26/0.54    inference(resolution,[],[f51,f55])).
% 1.26/0.54  fof(f303,plain,(
% 1.26/0.54    ~spl9_18),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f296])).
% 1.26/0.54  fof(f296,plain,(
% 1.26/0.54    $false | ~spl9_18),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f183,f108,f292,f82])).
% 1.26/0.54  fof(f292,plain,(
% 1.26/0.54    r1_tarski(sK3,k1_xboole_0) | ~spl9_18),
% 1.26/0.54    inference(superposition,[],[f78,f266])).
% 1.26/0.54  fof(f266,plain,(
% 1.26/0.54    k1_xboole_0 = sK0 | ~spl9_18),
% 1.26/0.54    inference(avatar_component_clause,[],[f264])).
% 1.26/0.54  fof(f78,plain,(
% 1.26/0.54    r1_tarski(sK3,sK0)),
% 1.26/0.54    inference(resolution,[],[f44,f30])).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  fof(f183,plain,(
% 1.26/0.54    ~v1_xboole_0(sK3)),
% 1.26/0.54    inference(resolution,[],[f181,f33])).
% 1.26/0.54  fof(f289,plain,(
% 1.26/0.54    spl9_22),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f286])).
% 1.26/0.54  fof(f286,plain,(
% 1.26/0.54    $false | spl9_22),
% 1.26/0.54    inference(subsumption_resolution,[],[f236,f282])).
% 1.26/0.54  fof(f282,plain,(
% 1.26/0.54    ~r2_hidden(k2_mcart_1(sK6),sK5) | spl9_22),
% 1.26/0.54    inference(avatar_component_clause,[],[f280])).
% 1.26/0.54  fof(f280,plain,(
% 1.26/0.54    spl9_22 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 1.26/0.54  fof(f285,plain,(
% 1.26/0.54    spl9_19),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f284])).
% 1.26/0.54  fof(f284,plain,(
% 1.26/0.54    $false | spl9_19),
% 1.26/0.54    inference(subsumption_resolution,[],[f56,f270])).
% 1.26/0.54  fof(f270,plain,(
% 1.26/0.54    ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl9_19),
% 1.26/0.54    inference(avatar_component_clause,[],[f268])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.26/0.54    inference(definition_unfolding,[],[f26,f47])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  fof(f283,plain,(
% 1.26/0.54    spl9_18 | ~spl9_19 | spl9_20 | spl9_21 | ~spl9_22 | spl9_1),
% 1.26/0.54    inference(avatar_split_clause,[],[f262,f63,f280,f276,f272,f268,f264])).
% 1.26/0.54  fof(f63,plain,(
% 1.26/0.54    spl9_1 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.26/0.54  fof(f262,plain,(
% 1.26/0.54    ~r2_hidden(k2_mcart_1(sK6),sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl9_1),
% 1.26/0.54    inference(superposition,[],[f65,f57])).
% 1.26/0.54  fof(f57,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.26/0.54    inference(definition_unfolding,[],[f54,f47])).
% 1.26/0.54  fof(f54,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f24])).
% 1.26/0.54  fof(f65,plain,(
% 1.26/0.54    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl9_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f63])).
% 1.26/0.54  fof(f74,plain,(
% 1.26/0.54    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 1.26/0.54    inference(avatar_split_clause,[],[f25,f71,f67,f63])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.26/0.54    inference(cnf_transformation,[],[f18])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (11075)------------------------------
% 1.26/0.54  % (11075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (11075)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (11075)Memory used [KB]: 6396
% 1.26/0.54  % (11075)Time elapsed: 0.121 s
% 1.26/0.54  % (11075)------------------------------
% 1.26/0.54  % (11075)------------------------------
% 1.26/0.54  % (11061)Success in time 0.171 s
%------------------------------------------------------------------------------
