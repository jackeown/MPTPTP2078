%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 212 expanded)
%              Number of leaves         :   29 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 ( 975 expanded)
%              Number of equality atoms :   76 ( 164 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f68,f72,f76,f80,f150,f162,f174,f196,f199,f205,f210,f216,f221,f227,f235,f247,f255,f263])).

fof(f263,plain,
    ( k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2)
    | r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f255,plain,
    ( spl7_19
    | spl7_4
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f253,f214,f66,f148])).

fof(f148,plain,
    ( spl7_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f66,plain,
    ( spl7_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f214,plain,
    ( spl7_29
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl7_29 ),
    inference(resolution,[],[f234,f51])).

fof(f51,plain,(
    ! [X0,X7,X5] :
      ( ~ r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X7,X0)
      | r2_hidden(X5,X7)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK4(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f234,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f214])).

fof(f247,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f244,f66,f61,f57])).

fof(f57,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f61,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f244,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f62,f67])).

fof(f67,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f62,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f235,plain,
    ( spl7_19
    | spl7_29
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f232,f225,f214,f148])).

fof(f225,plain,
    ( spl7_31
  <=> r2_hidden(sK1,sK6(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f232,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_31 ),
    inference(resolution,[],[f226,f49])).

fof(f49,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,sK6(X0,X5))
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK6(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f226,plain,
    ( r2_hidden(sK1,sK6(sK2,sK1))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f225])).

fof(f227,plain,
    ( spl7_31
    | ~ spl7_4
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f222,f219,f66,f225])).

fof(f219,plain,
    ( spl7_30
  <=> r2_hidden(sK6(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f222,plain,
    ( r2_hidden(sK1,sK6(sK2,sK1))
    | ~ spl7_4
    | ~ spl7_30 ),
    inference(resolution,[],[f220,f67])).

fof(f220,plain,
    ( r2_hidden(sK6(sK2,sK1),sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,
    ( spl7_19
    | spl7_30
    | spl7_29 ),
    inference(avatar_split_clause,[],[f217,f214,f219,f148])).

fof(f217,plain,
    ( r2_hidden(sK6(sK2,sK1),sK2)
    | k1_xboole_0 = sK2
    | spl7_29 ),
    inference(resolution,[],[f215,f50])).

fof(f50,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK6(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK6(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f215,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_29 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( ~ spl7_29
    | spl7_1
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f212,f159,f54,f214])).

fof(f54,plain,
    ( spl7_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f159,plain,
    ( spl7_21
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f212,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl7_1
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f55,f160])).

fof(f160,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f55,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f210,plain,
    ( ~ spl7_7
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(resolution,[],[f204,f86])).

fof(f86,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_7 ),
    inference(resolution,[],[f33,f79])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f204,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl7_28
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f205,plain,
    ( spl7_28
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f201,f148,f61,f203])).

fof(f201,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f62,f149])).

fof(f149,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f199,plain,
    ( k1_xboole_0 != sK2
    | sK0 != k8_setfam_1(sK0,k1_xboole_0)
    | ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f196,plain,
    ( spl7_27
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f191,f172,f194])).

fof(f194,plain,
    ( spl7_27
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f172,plain,
    ( spl7_23
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f191,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl7_23 ),
    inference(resolution,[],[f173,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f173,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl7_23
    | ~ spl7_6
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f165,f148,f74,f172])).

fof(f74,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f165,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_6
    | ~ spl7_19 ),
    inference(superposition,[],[f75,f149])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f162,plain,
    ( ~ spl7_6
    | spl7_21
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f156,f145,f159,f74])).

fof(f145,plain,
    ( spl7_18
  <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f156,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl7_18 ),
    inference(superposition,[],[f42,f146])).

fof(f146,plain,
    ( k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f150,plain,
    ( spl7_18
    | spl7_19
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f142,f74,f148,f145])).

fof(f142,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f43,f75])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f76,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f72,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f70,plain,
    ( spl7_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f28,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f29,f66,f54])).

fof(f29,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f30,f61,f54])).

fof(f30,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f31,f57,f54])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (7524)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.45  % (7515)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.45  % (7524)Refutation not found, incomplete strategy% (7524)------------------------------
% 0.21/0.45  % (7524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (7524)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (7524)Memory used [KB]: 6012
% 0.21/0.45  % (7524)Time elapsed: 0.049 s
% 0.21/0.45  % (7524)------------------------------
% 0.21/0.45  % (7524)------------------------------
% 0.21/0.47  % (7517)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (7518)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (7526)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (7517)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f59,f63,f68,f72,f76,f80,f150,f162,f174,f196,f199,f205,f210,f216,f221,f227,f235,f247,f255,f263])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2) | r2_hidden(sK1,k1_setfam_1(sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl7_19 | spl7_4 | ~spl7_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f253,f214,f66,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl7_19 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl7_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    spl7_29 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2) ) | ~spl7_29),
% 0.21/0.48    inference(resolution,[],[f234,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X7,X5] : (~r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X7,X0) | r2_hidden(X5,X7) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(equality_resolution,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.21/0.48    inference(rectify,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl7_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f214])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    spl7_2 | ~spl7_3 | ~spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f244,f66,f61,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl7_2 <=> r2_hidden(sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl7_3 <=> r2_hidden(sK3,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    r2_hidden(sK1,sK3) | (~spl7_3 | ~spl7_4)),
% 0.21/0.48    inference(resolution,[],[f62,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    r2_hidden(sK3,sK2) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    spl7_19 | spl7_29 | ~spl7_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f232,f225,f214,f148])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    spl7_31 <=> r2_hidden(sK1,sK6(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl7_31),
% 0.21/0.48    inference(resolution,[],[f226,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X5] : (~r2_hidden(X5,sK6(X0,X5)) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(equality_resolution,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK6(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    r2_hidden(sK1,sK6(sK2,sK1)) | ~spl7_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f225])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    spl7_31 | ~spl7_4 | ~spl7_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f222,f219,f66,f225])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    spl7_30 <=> r2_hidden(sK6(sK2,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    r2_hidden(sK1,sK6(sK2,sK1)) | (~spl7_4 | ~spl7_30)),
% 0.21/0.48    inference(resolution,[],[f220,f67])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    r2_hidden(sK6(sK2,sK1),sK2) | ~spl7_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f219])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl7_19 | spl7_30 | spl7_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f217,f214,f219,f148])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    r2_hidden(sK6(sK2,sK1),sK2) | k1_xboole_0 = sK2 | spl7_29),
% 0.21/0.48    inference(resolution,[],[f215,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X5] : (r2_hidden(X5,k1_setfam_1(X0)) | r2_hidden(sK6(X0,X5),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(equality_resolution,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK6(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_setfam_1(sK2)) | spl7_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f214])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ~spl7_29 | spl7_1 | ~spl7_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f212,f159,f54,f214])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl7_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl7_21 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_setfam_1(sK2)) | (spl7_1 | ~spl7_21)),
% 0.21/0.48    inference(forward_demodulation,[],[f55,f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl7_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f159])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~spl7_7 | ~spl7_28),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    $false | (~spl7_7 | ~spl7_28)),
% 0.21/0.48    inference(resolution,[],[f204,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_7),
% 0.21/0.48    inference(resolution,[],[f33,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl7_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl7_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    r2_hidden(sK3,k1_xboole_0) | ~spl7_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f203])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    spl7_28 <=> r2_hidden(sK3,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    spl7_28 | ~spl7_3 | ~spl7_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f201,f148,f61,f203])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    r2_hidden(sK3,k1_xboole_0) | (~spl7_3 | ~spl7_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f62,f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl7_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | sK0 != k8_setfam_1(sK0,k1_xboole_0) | ~r2_hidden(sK1,sK0) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    spl7_27 | ~spl7_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f191,f172,f194])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    spl7_27 <=> sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl7_23 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl7_23),
% 0.21/0.48    inference(resolution,[],[f173,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(equality_resolution,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl7_23 | ~spl7_6 | ~spl7_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f165,f148,f74,f172])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl7_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl7_6 | ~spl7_19)),
% 0.21/0.48    inference(superposition,[],[f75,f149])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ~spl7_6 | spl7_21 | ~spl7_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f156,f145,f159,f74])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl7_18 <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl7_18),
% 0.21/0.48    inference(superposition,[],[f42,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl7_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f145])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl7_18 | spl7_19 | ~spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f142,f74,f148,f145])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl7_6),
% 0.21/0.48    inference(resolution,[],[f43,f75])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f78])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f74])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(rectify,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl7_5 <=> r2_hidden(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    r2_hidden(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl7_1 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f66,f54])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~spl7_1 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f61,f54])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~spl7_1 | ~spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f57,f54])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7517)------------------------------
% 0.21/0.48  % (7517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7517)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7517)Memory used [KB]: 10746
% 0.21/0.48  % (7517)Time elapsed: 0.073 s
% 0.21/0.48  % (7517)------------------------------
% 0.21/0.48  % (7517)------------------------------
% 0.21/0.49  % (7508)Success in time 0.13 s
%------------------------------------------------------------------------------
