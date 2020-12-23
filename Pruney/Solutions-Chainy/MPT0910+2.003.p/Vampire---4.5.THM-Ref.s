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
% DateTime   : Thu Dec  3 12:59:25 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 383 expanded)
%              Number of leaves         :   27 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  504 (1802 expanded)
%              Number of equality atoms :  198 ( 873 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1098,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f387,f621,f807,f837,f1089,f1093,f1097])).

fof(f1097,plain,
    ( ~ spl11_1
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f1096])).

fof(f1096,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f1095,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1095,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | ~ spl11_1
    | ~ spl11_20 ),
    inference(resolution,[],[f1088,f859])).

fof(f859,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4))
    | ~ spl11_1 ),
    inference(resolution,[],[f141,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f141,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl11_1
  <=> r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1088,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1087,plain,
    ( spl11_20
  <=> ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1093,plain,
    ( ~ spl11_1
    | ~ spl11_19 ),
    inference(avatar_contradiction_clause,[],[f1092])).

fof(f1092,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f1091,f70])).

fof(f1091,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_1
    | ~ spl11_19 ),
    inference(resolution,[],[f1085,f141])).

fof(f1085,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1084,plain,
    ( spl11_19
  <=> ! [X1] :
        ( ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f1089,plain,
    ( spl11_19
    | spl11_20
    | ~ spl11_11
    | spl11_12 ),
    inference(avatar_split_clause,[],[f1082,f384,f380,f1087,f1084])).

fof(f380,plain,
    ( spl11_11
  <=> sP2(sK7,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f384,plain,
    ( spl11_12
  <=> sK6 = k2_mcart_1(k1_mcart_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1082,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1081,f1038])).

fof(f1038,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f1022,f381])).

fof(f381,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f380])).

fof(f1022,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(resolution,[],[f389,f110])).

fof(f110,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f62,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f62,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK6 != k6_mcart_1(sK3,sK4,sK5,sK7)
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X6
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f23,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK6 != k6_mcart_1(sK3,sK4,sK5,sK7)
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X6
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f389,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0)
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f114,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f99,f81])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f1081,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1080,f957])).

fof(f957,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f941,f381])).

fof(f941,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(resolution,[],[f391,f110])).

fof(f391,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(X3),X2)
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f115,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f100,f81])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f1080,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1079,f386])).

fof(f386,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(sK7))
    | spl11_12 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1079,plain,
    ( ! [X0,X1] :
        ( sK6 = k2_mcart_1(k1_mcart_1(sK7))
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_11 ),
    inference(trivial_inequality_removal,[],[f1077])).

fof(f1077,plain,
    ( ! [X0,X1] :
        ( sK6 = k2_mcart_1(k1_mcart_1(sK7))
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | sK7 != sK7
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3)
        | ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_11 ),
    inference(resolution,[],[f1072,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK4)
      | sK6 = k2_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(k2_mcart_1(X0),sK5)
      | sK7 != X0
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK3)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f188,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK7
      | k2_mcart_1(X0) = sK6
      | ~ m1_subset_1(X1,sK5)
      | ~ m1_subset_1(k2_mcart_1(X0),sK4)
      | ~ m1_subset_1(k1_mcart_1(X0),sK3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f109,f73])).

fof(f109,plain,(
    ! [X6,X7,X5] :
      ( sK7 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK6 = X6
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f63,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X6
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1072,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f1056,f381])).

fof(f1056,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(resolution,[],[f393,f110])).

fof(f393,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1)
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(superposition,[],[f116,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f101,f81])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f837,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f824,f143,f139])).

fof(f143,plain,
    ( spl11_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f824,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(resolution,[],[f110,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f807,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f806])).

fof(f806,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f805,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f805,plain,
    ( k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f804,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f40])).

fof(f804,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f784,f136])).

fof(f136,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f69,f131])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f71,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
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

fof(f784,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(superposition,[],[f721,f756])).

fof(f756,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f731,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f731,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl11_2 ),
    inference(resolution,[],[f721,f145])).

fof(f145,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f721,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f720])).

fof(f720,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X0)) ) ),
    inference(condensation,[],[f719])).

fof(f719,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(k2_zfmisc_1(X3,X2)) ) ),
    inference(subsumption_resolution,[],[f712,f339])).

fof(f339,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f209,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f209,plain,(
    ! [X6,X5] :
      ( r2_hidden(k1_mcart_1(sK9(k2_zfmisc_1(X5,X6),k1_xboole_0)),X5)
      | k1_xboole_0 = k2_zfmisc_1(X5,X6) ) ),
    inference(resolution,[],[f200,f83])).

fof(f200,plain,(
    ! [X11] :
      ( r2_hidden(sK9(X11,k1_xboole_0),X11)
      | k1_xboole_0 = X11 ) ),
    inference(resolution,[],[f75,f131])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f712,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(k2_zfmisc_1(X3,X2)) ) ),
    inference(condensation,[],[f680])).

fof(f680,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(X6,X7)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | ~ v1_xboole_0(X6)
      | ~ v1_xboole_0(k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f121,f466])).

fof(f466,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X1,X2) = X0
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f299,f68])).

fof(f299,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(k1_mcart_1(sK9(k2_zfmisc_1(X9,X10),X11)),X9)
      | ~ v1_xboole_0(X11)
      | k2_zfmisc_1(X9,X10) = X11 ) ),
    inference(resolution,[],[f196,f83])).

fof(f196,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f75,f68])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f102,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f98,f81])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f621,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f620,f380])).

fof(f620,plain,(
    sP2(sK7,sK5,sK4,sK3) ),
    inference(subsumption_resolution,[],[f619,f64])).

fof(f619,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f618,f65])).

fof(f618,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f597,f66])).

fof(f597,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f113,f110])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP2(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f97,f81])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP2(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f30,f37])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f387,plain,
    ( ~ spl11_11
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f378,f384,f380])).

fof(f378,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(sK7))
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(superposition,[],[f67,f95])).

fof(f67,plain,(
    sK6 != k6_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:18:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (20776)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.53  % (20778)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (20769)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (20785)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (20767)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.55  % (20766)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  % (20784)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (20777)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (20773)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.56  % (20785)Refutation not found, incomplete strategy% (20785)------------------------------
% 1.36/0.56  % (20785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (20787)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.56  % (20792)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.56  % (20793)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.56  % (20790)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.56  % (20779)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.56  % (20767)Refutation not found, incomplete strategy% (20767)------------------------------
% 1.36/0.56  % (20767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (20781)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.57  % (20765)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.57  % (20768)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.57  % (20785)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (20785)Memory used [KB]: 10874
% 1.36/0.57  % (20785)Time elapsed: 0.131 s
% 1.36/0.57  % (20785)------------------------------
% 1.36/0.57  % (20785)------------------------------
% 1.36/0.57  % (20765)Refutation not found, incomplete strategy% (20765)------------------------------
% 1.36/0.57  % (20765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (20765)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (20765)Memory used [KB]: 1791
% 1.36/0.57  % (20765)Time elapsed: 0.143 s
% 1.36/0.57  % (20765)------------------------------
% 1.36/0.57  % (20765)------------------------------
% 1.36/0.57  % (20771)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.57  % (20774)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.57  % (20767)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (20767)Memory used [KB]: 10746
% 1.36/0.57  % (20767)Time elapsed: 0.132 s
% 1.36/0.57  % (20767)------------------------------
% 1.36/0.57  % (20767)------------------------------
% 1.36/0.57  % (20770)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.57  % (20773)Refutation not found, incomplete strategy% (20773)------------------------------
% 1.36/0.57  % (20773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (20773)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (20773)Memory used [KB]: 10746
% 1.36/0.57  % (20773)Time elapsed: 0.153 s
% 1.36/0.57  % (20773)------------------------------
% 1.36/0.57  % (20773)------------------------------
% 1.36/0.57  % (20772)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.58  % (20780)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.58  % (20794)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.58  % (20791)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.58  % (20789)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.58  % (20782)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.58  % (20786)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.58  % (20788)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.58  % (20786)Refutation not found, incomplete strategy% (20786)------------------------------
% 1.36/0.58  % (20786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (20786)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (20786)Memory used [KB]: 1791
% 1.36/0.58  % (20786)Time elapsed: 0.145 s
% 1.36/0.58  % (20786)------------------------------
% 1.36/0.58  % (20786)------------------------------
% 1.36/0.58  % (20788)Refutation not found, incomplete strategy% (20788)------------------------------
% 1.36/0.58  % (20788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (20788)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (20788)Memory used [KB]: 1791
% 1.36/0.58  % (20788)Time elapsed: 0.165 s
% 1.36/0.58  % (20788)------------------------------
% 1.36/0.58  % (20788)------------------------------
% 1.36/0.58  % (20783)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.59  % (20787)Refutation not found, incomplete strategy% (20787)------------------------------
% 1.36/0.59  % (20787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.59  % (20787)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.59  
% 1.36/0.59  % (20787)Memory used [KB]: 10746
% 1.36/0.59  % (20787)Time elapsed: 0.137 s
% 1.36/0.59  % (20787)------------------------------
% 1.36/0.59  % (20787)------------------------------
% 1.36/0.59  % (20775)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.60  % (20782)Refutation not found, incomplete strategy% (20782)------------------------------
% 1.36/0.60  % (20782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.60  % (20782)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.60  
% 1.36/0.60  % (20782)Memory used [KB]: 10746
% 1.36/0.60  % (20782)Time elapsed: 0.149 s
% 1.36/0.60  % (20782)------------------------------
% 1.36/0.60  % (20782)------------------------------
% 1.36/0.63  % (20792)Refutation found. Thanks to Tanya!
% 1.36/0.63  % SZS status Theorem for theBenchmark
% 1.36/0.63  % SZS output start Proof for theBenchmark
% 1.36/0.63  fof(f1098,plain,(
% 1.36/0.63    $false),
% 1.36/0.63    inference(avatar_sat_refutation,[],[f387,f621,f807,f837,f1089,f1093,f1097])).
% 1.36/0.63  fof(f1097,plain,(
% 1.36/0.63    ~spl11_1 | ~spl11_20),
% 1.36/0.63    inference(avatar_contradiction_clause,[],[f1096])).
% 1.36/0.63  fof(f1096,plain,(
% 1.36/0.63    $false | (~spl11_1 | ~spl11_20)),
% 1.36/0.63    inference(subsumption_resolution,[],[f1095,f70])).
% 1.36/0.63  fof(f70,plain,(
% 1.36/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f9])).
% 1.36/0.63  fof(f9,axiom,(
% 1.36/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.63  fof(f1095,plain,(
% 1.36/0.63    ~v1_relat_1(k2_zfmisc_1(sK3,sK4)) | (~spl11_1 | ~spl11_20)),
% 1.36/0.63    inference(resolution,[],[f1088,f859])).
% 1.36/0.63  fof(f859,plain,(
% 1.36/0.63    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) | ~spl11_1),
% 1.36/0.63    inference(resolution,[],[f141,f83])).
% 1.36/0.63  fof(f83,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f29])).
% 1.36/0.63  fof(f29,plain,(
% 1.36/0.63    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.36/0.63    inference(ennf_transformation,[],[f16])).
% 1.36/0.63  fof(f16,axiom,(
% 1.36/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.36/0.63  fof(f141,plain,(
% 1.36/0.63    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl11_1),
% 1.36/0.63    inference(avatar_component_clause,[],[f139])).
% 1.36/0.63  fof(f139,plain,(
% 1.36/0.63    spl11_1 <=> r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.36/0.63  fof(f1088,plain,(
% 1.36/0.63    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0)) ) | ~spl11_20),
% 1.36/0.63    inference(avatar_component_clause,[],[f1087])).
% 1.36/0.63  fof(f1087,plain,(
% 1.36/0.63    spl11_20 <=> ! [X0] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 1.36/0.63  fof(f1093,plain,(
% 1.36/0.63    ~spl11_1 | ~spl11_19),
% 1.36/0.63    inference(avatar_contradiction_clause,[],[f1092])).
% 1.36/0.63  fof(f1092,plain,(
% 1.36/0.63    $false | (~spl11_1 | ~spl11_19)),
% 1.36/0.63    inference(subsumption_resolution,[],[f1091,f70])).
% 1.36/0.63  fof(f1091,plain,(
% 1.36/0.63    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | (~spl11_1 | ~spl11_19)),
% 1.36/0.63    inference(resolution,[],[f1085,f141])).
% 1.36/0.63  fof(f1085,plain,(
% 1.36/0.63    ( ! [X1] : (~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | ~spl11_19),
% 1.36/0.63    inference(avatar_component_clause,[],[f1084])).
% 1.36/0.63  fof(f1084,plain,(
% 1.36/0.63    spl11_19 <=> ! [X1] : (~r2_hidden(sK7,X1) | ~v1_relat_1(X1))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 1.36/0.63  fof(f1089,plain,(
% 1.36/0.63    spl11_19 | spl11_20 | ~spl11_11 | spl11_12),
% 1.36/0.63    inference(avatar_split_clause,[],[f1082,f384,f380,f1087,f1084])).
% 1.36/0.63  fof(f380,plain,(
% 1.36/0.63    spl11_11 <=> sP2(sK7,sK5,sK4,sK3)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.36/0.63  fof(f384,plain,(
% 1.36/0.63    spl11_12 <=> sK6 = k2_mcart_1(k1_mcart_1(sK7))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.36/0.63  fof(f1082,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | (~spl11_11 | spl11_12)),
% 1.36/0.63    inference(subsumption_resolution,[],[f1081,f1038])).
% 1.36/0.63  fof(f1038,plain,(
% 1.36/0.63    m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~spl11_11),
% 1.36/0.63    inference(subsumption_resolution,[],[f1022,f381])).
% 1.36/0.63  fof(f381,plain,(
% 1.36/0.63    sP2(sK7,sK5,sK4,sK3) | ~spl11_11),
% 1.36/0.63    inference(avatar_component_clause,[],[f380])).
% 1.36/0.63  fof(f1022,plain,(
% 1.36/0.63    m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~sP2(sK7,sK5,sK4,sK3)),
% 1.36/0.63    inference(resolution,[],[f389,f110])).
% 1.36/0.63  fof(f110,plain,(
% 1.36/0.63    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.36/0.63    inference(definition_unfolding,[],[f62,f81])).
% 1.36/0.63  fof(f81,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f11])).
% 1.36/0.63  fof(f11,axiom,(
% 1.36/0.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.36/0.63  fof(f62,plain,(
% 1.36/0.63    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.36/0.63    inference(cnf_transformation,[],[f40])).
% 1.36/0.63  fof(f40,plain,(
% 1.36/0.63    sK6 != k6_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.36/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f23,f39])).
% 1.36/0.63  fof(f39,plain,(
% 1.36/0.63    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK6 != k6_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 1.36/0.63    introduced(choice_axiom,[])).
% 1.36/0.63  fof(f23,plain,(
% 1.36/0.63    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.36/0.63    inference(flattening,[],[f22])).
% 1.36/0.63  fof(f22,plain,(
% 1.36/0.63    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.36/0.63    inference(ennf_transformation,[],[f21])).
% 1.36/0.63  fof(f21,negated_conjecture,(
% 1.36/0.63    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.36/0.63    inference(negated_conjecture,[],[f20])).
% 1.36/0.63  fof(f20,conjecture,(
% 1.36/0.63    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 1.36/0.63  fof(f389,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),X0) | ~sP2(X3,X2,X1,X0)) )),
% 1.36/0.63    inference(superposition,[],[f114,f94])).
% 1.36/0.63  fof(f94,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) | ~sP2(X0,X1,X2,X3)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f59])).
% 1.36/0.63  fof(f59,plain,(
% 1.36/0.63    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP2(X0,X1,X2,X3))),
% 1.36/0.63    inference(rectify,[],[f58])).
% 1.36/0.63  fof(f58,plain,(
% 1.36/0.63    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 1.36/0.63    inference(nnf_transformation,[],[f37])).
% 1.36/0.63  fof(f37,plain,(
% 1.36/0.63    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 1.36/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.36/0.63  fof(f114,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.36/0.63    inference(definition_unfolding,[],[f99,f81])).
% 1.36/0.63  fof(f99,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f31])).
% 1.36/0.63  fof(f31,plain,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.36/0.63    inference(ennf_transformation,[],[f13])).
% 1.36/0.63  fof(f13,axiom,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 1.36/0.63  fof(f1081,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | (~spl11_11 | spl11_12)),
% 1.36/0.63    inference(subsumption_resolution,[],[f1080,f957])).
% 1.36/0.63  fof(f957,plain,(
% 1.36/0.63    m1_subset_1(k2_mcart_1(sK7),sK5) | ~spl11_11),
% 1.36/0.63    inference(subsumption_resolution,[],[f941,f381])).
% 1.36/0.63  fof(f941,plain,(
% 1.36/0.63    m1_subset_1(k2_mcart_1(sK7),sK5) | ~sP2(sK7,sK5,sK4,sK3)),
% 1.36/0.63    inference(resolution,[],[f391,f110])).
% 1.36/0.63  fof(f391,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(X3),X2) | ~sP2(X3,X2,X1,X0)) )),
% 1.36/0.63    inference(superposition,[],[f115,f96])).
% 1.36/0.63  fof(f96,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP2(X0,X1,X2,X3)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f59])).
% 1.36/0.63  fof(f115,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.36/0.63    inference(definition_unfolding,[],[f100,f81])).
% 1.36/0.63  fof(f100,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f32])).
% 1.36/0.63  fof(f32,plain,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.36/0.63    inference(ennf_transformation,[],[f15])).
% 1.36/0.63  fof(f15,axiom,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.36/0.63  fof(f1080,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~m1_subset_1(k2_mcart_1(sK7),sK5) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | (~spl11_11 | spl11_12)),
% 1.36/0.63    inference(subsumption_resolution,[],[f1079,f386])).
% 1.36/0.63  fof(f386,plain,(
% 1.36/0.63    sK6 != k2_mcart_1(k1_mcart_1(sK7)) | spl11_12),
% 1.36/0.63    inference(avatar_component_clause,[],[f384])).
% 1.36/0.63  fof(f1079,plain,(
% 1.36/0.63    ( ! [X0,X1] : (sK6 = k2_mcart_1(k1_mcart_1(sK7)) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | ~spl11_11),
% 1.36/0.63    inference(trivial_inequality_removal,[],[f1077])).
% 1.36/0.63  fof(f1077,plain,(
% 1.36/0.63    ( ! [X0,X1] : (sK6 = k2_mcart_1(k1_mcart_1(sK7)) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | sK7 != sK7 | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) | ~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | ~spl11_11),
% 1.36/0.63    inference(resolution,[],[f1072,f189])).
% 1.36/0.63  fof(f189,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK4) | sK6 = k2_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(k2_mcart_1(X0),sK5) | sK7 != X0 | ~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK3) | ~r2_hidden(k1_mcart_1(X0),X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.36/0.63    inference(superposition,[],[f188,f73])).
% 1.36/0.63  fof(f73,plain,(
% 1.36/0.63    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f25])).
% 1.36/0.63  fof(f25,plain,(
% 1.36/0.63    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.36/0.63    inference(flattening,[],[f24])).
% 1.36/0.63  fof(f24,plain,(
% 1.36/0.63    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.36/0.63    inference(ennf_transformation,[],[f17])).
% 1.36/0.63  fof(f17,axiom,(
% 1.36/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.36/0.63  fof(f188,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK7 | k2_mcart_1(X0) = sK6 | ~m1_subset_1(X1,sK5) | ~m1_subset_1(k2_mcart_1(X0),sK4) | ~m1_subset_1(k1_mcart_1(X0),sK3) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.36/0.63    inference(superposition,[],[f109,f73])).
% 1.36/0.63  fof(f109,plain,(
% 1.36/0.63    ( ! [X6,X7,X5] : (sK7 != k4_tarski(k4_tarski(X5,X6),X7) | sK6 = X6 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 1.36/0.63    inference(definition_unfolding,[],[f63,f80])).
% 1.36/0.63  fof(f80,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f10])).
% 1.36/0.63  fof(f10,axiom,(
% 1.36/0.63    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.36/0.63  fof(f63,plain,(
% 1.36/0.63    ( ! [X6,X7,X5] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f40])).
% 1.36/0.63  fof(f1072,plain,(
% 1.36/0.63    m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~spl11_11),
% 1.36/0.63    inference(subsumption_resolution,[],[f1056,f381])).
% 1.36/0.63  fof(f1056,plain,(
% 1.36/0.63    m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) | ~sP2(sK7,sK5,sK4,sK3)),
% 1.36/0.63    inference(resolution,[],[f393,f110])).
% 1.36/0.63  fof(f393,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),X1) | ~sP2(X3,X2,X1,X0)) )),
% 1.36/0.63    inference(superposition,[],[f116,f95])).
% 1.36/0.63  fof(f95,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) | ~sP2(X0,X1,X2,X3)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f59])).
% 1.36/0.63  fof(f116,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.36/0.63    inference(definition_unfolding,[],[f101,f81])).
% 1.36/0.63  fof(f101,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f33])).
% 1.36/0.63  fof(f33,plain,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.36/0.63    inference(ennf_transformation,[],[f14])).
% 1.36/0.63  fof(f14,axiom,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 1.36/0.63  fof(f837,plain,(
% 1.36/0.63    spl11_1 | spl11_2),
% 1.36/0.63    inference(avatar_split_clause,[],[f824,f143,f139])).
% 1.36/0.63  fof(f143,plain,(
% 1.36/0.63    spl11_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.36/0.63  fof(f824,plain,(
% 1.36/0.63    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.36/0.63    inference(resolution,[],[f110,f74])).
% 1.36/0.63  fof(f74,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f27])).
% 1.36/0.63  fof(f27,plain,(
% 1.36/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.36/0.63    inference(flattening,[],[f26])).
% 1.36/0.63  fof(f26,plain,(
% 1.36/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.36/0.63    inference(ennf_transformation,[],[f8])).
% 1.36/0.63  fof(f8,axiom,(
% 1.36/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.36/0.63  fof(f807,plain,(
% 1.36/0.63    ~spl11_2),
% 1.36/0.63    inference(avatar_contradiction_clause,[],[f806])).
% 1.36/0.63  fof(f806,plain,(
% 1.36/0.63    $false | ~spl11_2),
% 1.36/0.63    inference(subsumption_resolution,[],[f805,f64])).
% 1.36/0.63  fof(f64,plain,(
% 1.36/0.63    k1_xboole_0 != sK3),
% 1.36/0.63    inference(cnf_transformation,[],[f40])).
% 1.36/0.63  fof(f805,plain,(
% 1.36/0.63    k1_xboole_0 = sK3 | ~spl11_2),
% 1.36/0.63    inference(subsumption_resolution,[],[f804,f65])).
% 1.36/0.63  fof(f65,plain,(
% 1.36/0.63    k1_xboole_0 != sK4),
% 1.36/0.63    inference(cnf_transformation,[],[f40])).
% 1.36/0.63  fof(f804,plain,(
% 1.36/0.63    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl11_2),
% 1.36/0.63    inference(subsumption_resolution,[],[f784,f136])).
% 1.36/0.63  fof(f136,plain,(
% 1.36/0.63    v1_xboole_0(k1_xboole_0)),
% 1.36/0.63    inference(resolution,[],[f69,f131])).
% 1.36/0.63  fof(f131,plain,(
% 1.36/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.36/0.63    inference(superposition,[],[f71,f122])).
% 1.36/0.63  fof(f122,plain,(
% 1.36/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.36/0.63    inference(equality_resolution,[],[f79])).
% 1.36/0.63  fof(f79,plain,(
% 1.36/0.63    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.36/0.63    inference(cnf_transformation,[],[f49])).
% 1.36/0.63  fof(f49,plain,(
% 1.36/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.36/0.63    inference(flattening,[],[f48])).
% 1.36/0.63  fof(f48,plain,(
% 1.36/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.36/0.63    inference(nnf_transformation,[],[f6])).
% 1.36/0.63  fof(f6,axiom,(
% 1.36/0.63    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.36/0.63  fof(f71,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f7])).
% 1.36/0.63  fof(f7,axiom,(
% 1.36/0.63    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.36/0.63  fof(f69,plain,(
% 1.36/0.63    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_xboole_0(X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f44])).
% 1.36/0.63  fof(f44,plain,(
% 1.36/0.63    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f43])).
% 1.36/0.63  fof(f43,plain,(
% 1.36/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 1.36/0.63    introduced(choice_axiom,[])).
% 1.36/0.63  fof(f42,plain,(
% 1.36/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.63    inference(rectify,[],[f41])).
% 1.36/0.63  fof(f41,plain,(
% 1.36/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.63    inference(nnf_transformation,[],[f1])).
% 1.36/0.63  fof(f1,axiom,(
% 1.36/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.63  fof(f784,plain,(
% 1.36/0.63    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl11_2),
% 1.36/0.63    inference(superposition,[],[f721,f756])).
% 1.36/0.63  fof(f756,plain,(
% 1.36/0.63    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl11_2),
% 1.36/0.63    inference(subsumption_resolution,[],[f731,f66])).
% 1.36/0.63  fof(f66,plain,(
% 1.36/0.63    k1_xboole_0 != sK5),
% 1.36/0.63    inference(cnf_transformation,[],[f40])).
% 1.36/0.63  fof(f731,plain,(
% 1.36/0.63    k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl11_2),
% 1.36/0.63    inference(resolution,[],[f721,f145])).
% 1.36/0.63  fof(f145,plain,(
% 1.36/0.63    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl11_2),
% 1.36/0.63    inference(avatar_component_clause,[],[f143])).
% 1.36/0.63  fof(f721,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.36/0.63    inference(condensation,[],[f720])).
% 1.36/0.63  fof(f720,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~v1_xboole_0(X2) | ~v1_xboole_0(k2_zfmisc_1(X1,X0))) )),
% 1.36/0.63    inference(condensation,[],[f719])).
% 1.36/0.63  fof(f719,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~v1_xboole_0(X1) | ~v1_xboole_0(k2_zfmisc_1(X3,X2))) )),
% 1.36/0.63    inference(subsumption_resolution,[],[f712,f339])).
% 1.36/0.63  fof(f339,plain,(
% 1.36/0.63    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~v1_xboole_0(X0)) )),
% 1.36/0.63    inference(resolution,[],[f209,f68])).
% 1.36/0.63  fof(f68,plain,(
% 1.36/0.63    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f44])).
% 1.36/0.63  fof(f209,plain,(
% 1.36/0.63    ( ! [X6,X5] : (r2_hidden(k1_mcart_1(sK9(k2_zfmisc_1(X5,X6),k1_xboole_0)),X5) | k1_xboole_0 = k2_zfmisc_1(X5,X6)) )),
% 1.36/0.63    inference(resolution,[],[f200,f83])).
% 1.36/0.63  fof(f200,plain,(
% 1.36/0.63    ( ! [X11] : (r2_hidden(sK9(X11,k1_xboole_0),X11) | k1_xboole_0 = X11) )),
% 1.36/0.63    inference(resolution,[],[f75,f131])).
% 1.36/0.63  fof(f75,plain,(
% 1.36/0.63    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | X0 = X1 | r2_hidden(sK9(X0,X1),X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f47])).
% 1.36/0.63  fof(f47,plain,(
% 1.36/0.63    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 1.36/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).
% 1.36/0.63  fof(f46,plain,(
% 1.36/0.63    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 1.36/0.63    introduced(choice_axiom,[])).
% 1.36/0.63  fof(f45,plain,(
% 1.36/0.63    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.36/0.63    inference(nnf_transformation,[],[f28])).
% 1.36/0.63  fof(f28,plain,(
% 1.36/0.63    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.36/0.63    inference(ennf_transformation,[],[f2])).
% 1.36/0.63  fof(f2,axiom,(
% 1.36/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.36/0.63  fof(f712,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~v1_xboole_0(X1) | ~v1_xboole_0(k2_zfmisc_1(X3,X2))) )),
% 1.36/0.63    inference(condensation,[],[f680])).
% 1.36/0.63  fof(f680,plain,(
% 1.36/0.63    ( ! [X6,X4,X7,X5,X3] : (k1_xboole_0 != k2_zfmisc_1(X6,X7) | k1_xboole_0 = X7 | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3 | ~v1_xboole_0(X6) | ~v1_xboole_0(k2_zfmisc_1(X3,X4))) )),
% 1.36/0.63    inference(superposition,[],[f121,f466])).
% 1.36/0.63  fof(f466,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(X1,X2) = X0 | ~v1_xboole_0(X0) | ~v1_xboole_0(X1)) )),
% 1.36/0.63    inference(resolution,[],[f299,f68])).
% 1.36/0.63  fof(f299,plain,(
% 1.36/0.63    ( ! [X10,X11,X9] : (r2_hidden(k1_mcart_1(sK9(k2_zfmisc_1(X9,X10),X11)),X9) | ~v1_xboole_0(X11) | k2_zfmisc_1(X9,X10) = X11) )),
% 1.36/0.63    inference(resolution,[],[f196,f83])).
% 1.36/0.63  fof(f196,plain,(
% 1.36/0.63    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.36/0.63    inference(resolution,[],[f75,f68])).
% 1.36/0.63  fof(f121,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.36/0.63    inference(definition_unfolding,[],[f102,f108])).
% 1.36/0.63  fof(f108,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.36/0.63    inference(definition_unfolding,[],[f98,f81])).
% 1.36/0.63  fof(f98,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f12])).
% 1.36/0.63  fof(f12,axiom,(
% 1.36/0.63    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.36/0.63  fof(f102,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.36/0.63    inference(cnf_transformation,[],[f61])).
% 1.36/0.63  fof(f61,plain,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.63    inference(flattening,[],[f60])).
% 1.36/0.63  fof(f60,plain,(
% 1.36/0.63    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.36/0.63    inference(nnf_transformation,[],[f19])).
% 1.36/0.63  fof(f19,axiom,(
% 1.36/0.63    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 1.36/0.63  fof(f621,plain,(
% 1.36/0.63    spl11_11),
% 1.36/0.63    inference(avatar_split_clause,[],[f620,f380])).
% 1.36/0.63  fof(f620,plain,(
% 1.36/0.63    sP2(sK7,sK5,sK4,sK3)),
% 1.36/0.63    inference(subsumption_resolution,[],[f619,f64])).
% 1.36/0.63  fof(f619,plain,(
% 1.36/0.63    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK3),
% 1.36/0.63    inference(subsumption_resolution,[],[f618,f65])).
% 1.36/0.63  fof(f618,plain,(
% 1.36/0.63    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 1.36/0.63    inference(subsumption_resolution,[],[f597,f66])).
% 1.36/0.63  fof(f597,plain,(
% 1.36/0.63    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 1.36/0.63    inference(resolution,[],[f113,f110])).
% 1.36/0.63  fof(f113,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP2(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.36/0.63    inference(definition_unfolding,[],[f97,f81])).
% 1.36/0.63  fof(f97,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.36/0.63    inference(cnf_transformation,[],[f38])).
% 1.36/0.63  fof(f38,plain,(
% 1.36/0.63    ! [X0,X1,X2] : (! [X3] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.36/0.63    inference(definition_folding,[],[f30,f37])).
% 1.36/0.63  fof(f30,plain,(
% 1.36/0.63    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.36/0.63    inference(ennf_transformation,[],[f18])).
% 1.36/0.63  fof(f18,axiom,(
% 1.36/0.63    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.36/0.63  fof(f387,plain,(
% 1.36/0.63    ~spl11_11 | ~spl11_12),
% 1.36/0.63    inference(avatar_split_clause,[],[f378,f384,f380])).
% 1.36/0.63  fof(f378,plain,(
% 1.36/0.63    sK6 != k2_mcart_1(k1_mcart_1(sK7)) | ~sP2(sK7,sK5,sK4,sK3)),
% 1.36/0.63    inference(superposition,[],[f67,f95])).
% 1.36/0.63  fof(f67,plain,(
% 1.36/0.63    sK6 != k6_mcart_1(sK3,sK4,sK5,sK7)),
% 1.36/0.63    inference(cnf_transformation,[],[f40])).
% 1.36/0.63  % SZS output end Proof for theBenchmark
% 1.36/0.63  % (20792)------------------------------
% 1.36/0.63  % (20792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.63  % (20792)Termination reason: Refutation
% 1.36/0.63  
% 1.36/0.63  % (20792)Memory used [KB]: 6652
% 1.36/0.63  % (20792)Time elapsed: 0.206 s
% 1.36/0.63  % (20792)------------------------------
% 1.36/0.63  % (20792)------------------------------
% 2.05/0.63  % (20764)Success in time 0.269 s
%------------------------------------------------------------------------------
