%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 209 expanded)
%              Number of leaves         :   27 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 ( 973 expanded)
%              Number of equality atoms :   84 ( 171 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f74,f78,f82,f109,f123,f129,f143,f149,f154,f178,f187,f196,f200,f210,f217,f220])).

fof(f220,plain,
    ( k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2)
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f217,plain,
    ( spl7_10
    | spl7_4
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f215,f185,f72,f104])).

fof(f104,plain,
    ( spl7_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f72,plain,
    ( spl7_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f185,plain,
    ( spl7_21
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl7_21 ),
    inference(resolution,[],[f199,f57])).

fof(f57,plain,(
    ! [X0,X7,X5] :
      ( ~ r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X7,X0)
      | r2_hidden(X5,X7)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),X0) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK4(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK6(X0,X5))
                    & r2_hidden(sK6(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK4(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f199,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f210,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f207,f72,f67,f63])).

fof(f63,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f67,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f207,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f73])).

fof(f73,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f68,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f200,plain,
    ( spl7_10
    | spl7_21
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f197,f194,f185,f104])).

fof(f194,plain,
    ( spl7_22
  <=> r2_hidden(sK1,sK6(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f197,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_22 ),
    inference(resolution,[],[f195,f55])).

fof(f55,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,sK6(X0,X5))
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK6(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f195,plain,
    ( r2_hidden(sK1,sK6(sK2,sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl7_22
    | ~ spl7_11
    | spl7_21 ),
    inference(avatar_split_clause,[],[f191,f185,f107,f194])).

fof(f107,plain,
    ( spl7_11
  <=> ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | r2_hidden(sK1,sK6(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f191,plain,
    ( r2_hidden(sK1,sK6(sK2,sK1))
    | ~ spl7_11
    | spl7_21 ),
    inference(resolution,[],[f186,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | r2_hidden(sK1,sK6(sK2,X0)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f186,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( ~ spl7_21
    | spl7_1
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f182,f176,f60,f185])).

fof(f60,plain,
    ( spl7_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f176,plain,
    ( spl7_19
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f182,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_1
    | ~ spl7_19 ),
    inference(superposition,[],[f61,f177])).

fof(f177,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f61,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f178,plain,
    ( spl7_19
    | spl7_10
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f172,f80,f104,f176])).

fof(f80,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f172,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f171,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f171,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f154,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl7_15 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl7_15 ),
    inference(superposition,[],[f128,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f128,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_tarski(sK3))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_15
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f149,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl7_17 ),
    inference(resolution,[],[f141,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f141,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_17
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f143,plain,
    ( ~ spl7_17
    | ~ spl7_5
    | spl7_14 ),
    inference(avatar_split_clause,[],[f138,f121,f76,f140])).

fof(f76,plain,
    ( spl7_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f121,plain,
    ( spl7_14
  <=> r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f138,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl7_14 ),
    inference(superposition,[],[f122,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f129,plain,
    ( ~ spl7_15
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f125,f104,f67,f127])).

fof(f125,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_tarski(sK3))
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f124,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f124,plain,
    ( sK2 != k4_xboole_0(sK2,k1_tarski(sK3))
    | ~ spl7_3 ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f123,plain,
    ( ~ spl7_14
    | spl7_1
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f119,f104,f60,f121])).

fof(f119,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl7_1
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f61,f105])).

fof(f109,plain,
    ( spl7_10
    | spl7_11
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f101,f72,f107,f104])).

fof(f101,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_setfam_1(sK2))
        | k1_xboole_0 = sK2
        | r2_hidden(sK1,sK6(sK2,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f56,f73])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),X0)
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK6(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK1,X3)
            & r2_hidden(X3,sK2) )
        | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & ( ! [X4] :
            ( r2_hidden(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & r2_hidden(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f78,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f32,f72,f60])).

fof(f32,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f33,f67,f60])).

fof(f33,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f34,f63,f60])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:06:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (18902)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (18903)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (18895)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (18895)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f65,f69,f74,f78,f82,f109,f123,f129,f143,f149,f154,f178,f187,f196,f200,f210,f217,f220])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2) | r2_hidden(sK1,k1_setfam_1(sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl7_10 | spl7_4 | ~spl7_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f215,f185,f72,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl7_10 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl7_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    spl7_21 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | ~spl7_21),
% 0.22/0.49    inference(resolution,[],[f199,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X7,X5] : (~r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X7,X0) | r2_hidden(X5,X7) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(equality_resolution,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.22/0.49    inference(rectify,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl7_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f185])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    spl7_2 | ~spl7_3 | ~spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f207,f72,f67,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl7_2 <=> r2_hidden(sK1,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl7_3 <=> r2_hidden(sK3,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    r2_hidden(sK1,sK3) | (~spl7_3 | ~spl7_4)),
% 0.22/0.49    inference(resolution,[],[f68,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl7_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    r2_hidden(sK3,sK2) | ~spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    spl7_10 | spl7_21 | ~spl7_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f197,f194,f185,f104])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    spl7_22 <=> r2_hidden(sK1,sK6(sK2,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_22),
% 0.22/0.49    inference(resolution,[],[f195,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X5] : (~r2_hidden(X5,sK6(X0,X5)) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(equality_resolution,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK6(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    r2_hidden(sK1,sK6(sK2,sK1)) | ~spl7_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f194])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    spl7_22 | ~spl7_11 | spl7_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f191,f185,f107,f194])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl7_11 <=> ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | r2_hidden(sK1,sK6(sK2,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    r2_hidden(sK1,sK6(sK2,sK1)) | (~spl7_11 | spl7_21)),
% 0.22/0.49    inference(resolution,[],[f186,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | r2_hidden(sK1,sK6(sK2,X0))) ) | ~spl7_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k1_setfam_1(sK2)) | spl7_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f185])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ~spl7_21 | spl7_1 | ~spl7_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f182,f176,f60,f185])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl7_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl7_19 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k1_setfam_1(sK2)) | (spl7_1 | ~spl7_19)),
% 0.22/0.49    inference(superposition,[],[f61,f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl7_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    spl7_19 | spl7_10 | ~spl7_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f172,f80,f104,f176])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl7_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl7_6),
% 0.22/0.49    inference(resolution,[],[f171,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f168])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.22/0.49    inference(superposition,[],[f46,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl7_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    $false | spl7_15),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f152])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    k1_xboole_0 != k1_xboole_0 | spl7_15),
% 0.22/0.49    inference(superposition,[],[f128,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_tarski(sK3)) | spl7_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl7_15 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl7_17),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f147])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    $false | spl7_17),
% 0.22/0.49    inference(resolution,[],[f141,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl7_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    spl7_17 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~spl7_17 | ~spl7_5 | spl7_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f138,f121,f76,f140])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl7_5 <=> r2_hidden(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl7_14 <=> r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~r2_hidden(sK1,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl7_14),
% 0.22/0.49    inference(superposition,[],[f122,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.49    inference(equality_resolution,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | spl7_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f121])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ~spl7_15 | ~spl7_3 | ~spl7_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f125,f104,f67,f127])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_tarski(sK3)) | (~spl7_3 | ~spl7_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f124,f105])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl7_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) | ~spl7_3),
% 0.22/0.49    inference(resolution,[],[f68,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ~spl7_14 | spl7_1 | ~spl7_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f119,f104,f60,f121])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl7_1 | ~spl7_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f61,f105])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl7_10 | spl7_11 | ~spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f101,f72,f107,f104])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | r2_hidden(sK1,sK6(sK2,X0))) ) | ~spl7_4),
% 0.22/0.49    inference(resolution,[],[f56,f73])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),X0) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(equality_resolution,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK6(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl7_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f80])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(rectify,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(nnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f76])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    r2_hidden(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl7_1 | spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f72,f60])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ~spl7_1 | spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f67,f60])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ~spl7_1 | ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f63,f60])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18895)------------------------------
% 0.22/0.49  % (18895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18895)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18895)Memory used [KB]: 10746
% 0.22/0.49  % (18895)Time elapsed: 0.013 s
% 0.22/0.49  % (18895)------------------------------
% 0.22/0.49  % (18895)------------------------------
% 0.22/0.49  % (18886)Success in time 0.129 s
%------------------------------------------------------------------------------
