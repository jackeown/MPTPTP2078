%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:29 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 637 expanded)
%              Number of leaves         :   36 ( 194 expanded)
%              Depth                    :   19
%              Number of atoms          :  573 (2755 expanded)
%              Number of equality atoms :  222 (1412 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1291,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f607,f804,f1078,f1102,f1144,f1168,f1210,f1232,f1266,f1274,f1277,f1286,f1290])).

fof(f1290,plain,
    ( spl14_1
    | spl14_41 ),
    inference(avatar_contradiction_clause,[],[f1289])).

fof(f1289,plain,
    ( $false
    | spl14_1
    | spl14_41 ),
    inference(subsumption_resolution,[],[f1288,f138])).

fof(f138,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK4)
    | spl14_1 ),
    inference(resolution,[],[f82,f130])).

fof(f130,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | spl14_1 ),
    inference(subsumption_resolution,[],[f127,f119])).

fof(f119,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | spl14_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl14_1
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f127,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(resolution,[],[f74,f96])).

fof(f96,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f54,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f1288,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK4)
    | spl14_41 ),
    inference(resolution,[],[f1265,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f1265,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK6),sK4)
    | spl14_41 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f1263,plain,
    ( spl14_41
  <=> m1_subset_1(k2_mcart_1(sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_41])])).

fof(f1286,plain,
    ( spl14_38
    | ~ spl14_36
    | spl14_40 ),
    inference(avatar_split_clause,[],[f1285,f1259,f1220,f1252])).

fof(f1252,plain,
    ( spl14_38
  <=> ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f1220,plain,
    ( spl14_36
  <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f1259,plain,
    ( spl14_40
  <=> m1_subset_1(sK9(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f1285,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl14_36
    | spl14_40 ),
    inference(subsumption_resolution,[],[f1284,f1221])).

fof(f1221,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl14_36 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
        | ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | spl14_40 ),
    inference(superposition,[],[f1261,f468])).

fof(f468,plain,(
    ! [X6,X7] :
      ( sK9(X6) = k2_mcart_1(X6)
      | ~ r2_hidden(X6,X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f73,f61])).

fof(f61,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK8(X4),sK9(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK7(X0)
          & r2_hidden(sK7(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK8(X4),sK9(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f37,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK7(X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK8(X4),sK9(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f1261,plain,
    ( ~ m1_subset_1(sK9(k1_mcart_1(sK6)),sK3)
    | spl14_40 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f1277,plain,
    ( spl14_1
    | ~ spl14_38 ),
    inference(avatar_contradiction_clause,[],[f1276])).

fof(f1276,plain,
    ( $false
    | spl14_1
    | ~ spl14_38 ),
    inference(subsumption_resolution,[],[f1275,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1275,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | spl14_1
    | ~ spl14_38 ),
    inference(resolution,[],[f1253,f132])).

fof(f132,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3))
    | spl14_1 ),
    inference(resolution,[],[f81,f130])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1253,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f1274,plain,
    ( spl14_38
    | spl14_1
    | spl14_39 ),
    inference(avatar_split_clause,[],[f1273,f1255,f117,f1252])).

fof(f1255,plain,
    ( spl14_39
  <=> m1_subset_1(sK8(k1_mcart_1(sK6)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_39])])).

fof(f1273,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | spl14_1
    | spl14_39 ),
    inference(subsumption_resolution,[],[f1272,f136])).

fof(f136,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2)
    | spl14_1 ),
    inference(resolution,[],[f132,f81])).

fof(f1272,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2)
        | ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | spl14_39 ),
    inference(superposition,[],[f1268,f469])).

fof(f469,plain,(
    ! [X8,X9] :
      ( sK8(X8) = k1_mcart_1(X8)
      | ~ r2_hidden(X8,X9)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f72,f61])).

fof(f72,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1268,plain,
    ( ~ r2_hidden(sK8(k1_mcart_1(sK6)),sK2)
    | spl14_39 ),
    inference(resolution,[],[f1257,f78])).

fof(f1257,plain,
    ( ~ m1_subset_1(sK8(k1_mcart_1(sK6)),sK2)
    | spl14_39 ),
    inference(avatar_component_clause,[],[f1255])).

fof(f1266,plain,
    ( spl14_38
    | ~ spl14_39
    | ~ spl14_40
    | ~ spl14_41
    | spl14_18
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f1250,f1165,f604,f1263,f1259,f1255,f1252])).

fof(f604,plain,
    ( spl14_18
  <=> sK5 = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f1165,plain,
    ( spl14_32
  <=> sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f1250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_mcart_1(sK6),sK4)
        | ~ m1_subset_1(sK9(k1_mcart_1(sK6)),sK3)
        | ~ m1_subset_1(sK8(k1_mcart_1(sK6)),sK2)
        | ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | spl14_18
    | ~ spl14_32 ),
    inference(subsumption_resolution,[],[f1249,f606])).

fof(f606,plain,
    ( sK5 != k2_mcart_1(sK6)
    | spl14_18 ),
    inference(avatar_component_clause,[],[f604])).

fof(f1249,plain,
    ( ! [X0] :
        ( sK5 = k2_mcart_1(sK6)
        | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
        | ~ m1_subset_1(sK9(k1_mcart_1(sK6)),sK3)
        | ~ m1_subset_1(sK8(k1_mcart_1(sK6)),sK2)
        | ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl14_32 ),
    inference(trivial_inequality_removal,[],[f1245])).

fof(f1245,plain,
    ( ! [X0] :
        ( sK6 != sK6
        | sK5 = k2_mcart_1(sK6)
        | ~ m1_subset_1(k2_mcart_1(sK6),sK4)
        | ~ m1_subset_1(sK9(k1_mcart_1(sK6)),sK3)
        | ~ m1_subset_1(sK8(k1_mcart_1(sK6)),sK2)
        | ~ r2_hidden(k1_mcart_1(sK6),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl14_32 ),
    inference(superposition,[],[f467,f1167])).

fof(f1167,plain,
    ( sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f467,plain,(
    ! [X4,X5,X3] :
      ( k4_tarski(X3,X4) != sK6
      | sK5 = X4
      | ~ m1_subset_1(X4,sK4)
      | ~ m1_subset_1(sK9(X3),sK3)
      | ~ m1_subset_1(sK8(X3),sK2)
      | ~ r2_hidden(X3,X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f95,f61])).

fof(f95,plain,(
    ! [X6,X7,X5] :
      ( sK6 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK5 = X7
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f55,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1232,plain,
    ( spl14_36
    | spl14_1
    | ~ spl14_15 ),
    inference(avatar_split_clause,[],[f1231,f591,f117,f1220])).

fof(f591,plain,
    ( spl14_15
  <=> m1_subset_1(sK13(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f1231,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl14_1
    | ~ spl14_15 ),
    inference(forward_demodulation,[],[f592,f1133])).

fof(f1133,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) = sK13(k1_mcart_1(sK6))
    | spl14_1 ),
    inference(resolution,[],[f132,f513])).

fof(f513,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X9,X10))
      | k2_mcart_1(X8) = sK13(X8) ) ),
    inference(superposition,[],[f73,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK12(X0),sK13(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK12(X0),sK13(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f27,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK12(X0),sK13(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f592,plain,
    ( m1_subset_1(sK13(k1_mcart_1(sK6)),sK3)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f591])).

fof(f1210,plain,
    ( spl14_1
    | spl14_15 ),
    inference(avatar_contradiction_clause,[],[f1209])).

fof(f1209,plain,
    ( $false
    | spl14_1
    | spl14_15 ),
    inference(subsumption_resolution,[],[f1206,f139])).

fof(f139,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl14_1 ),
    inference(resolution,[],[f82,f132])).

fof(f1206,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3)
    | spl14_1
    | spl14_15 ),
    inference(backward_demodulation,[],[f611,f1133])).

fof(f611,plain,
    ( ~ r2_hidden(sK13(k1_mcart_1(sK6)),sK3)
    | spl14_15 ),
    inference(resolution,[],[f593,f78])).

fof(f593,plain,
    ( ~ m1_subset_1(sK13(k1_mcart_1(sK6)),sK3)
    | spl14_15 ),
    inference(avatar_component_clause,[],[f591])).

fof(f1168,plain,
    ( spl14_19
    | spl14_32
    | spl14_1
    | ~ spl14_27 ),
    inference(avatar_split_clause,[],[f1163,f677,f117,f1165,f638])).

fof(f638,plain,
    ( spl14_19
  <=> ! [X1,X0] : ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f677,plain,
    ( spl14_27
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f1163,plain,
    ( ! [X0,X1] :
        ( sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))
        | ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1)) )
    | spl14_1
    | ~ spl14_27 ),
    inference(forward_demodulation,[],[f1162,f618])).

fof(f618,plain,
    ( k2_mcart_1(sK6) = sK13(sK6)
    | spl14_1 ),
    inference(resolution,[],[f513,f130])).

fof(f1162,plain,
    ( ! [X0,X1] :
        ( sK6 = k4_tarski(k1_mcart_1(sK6),sK13(sK6))
        | ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1)) )
    | ~ spl14_27 ),
    inference(superposition,[],[f87,f1145])).

fof(f1145,plain,
    ( k1_mcart_1(sK6) = sK12(sK6)
    | ~ spl14_27 ),
    inference(resolution,[],[f679,f514])).

fof(f514,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X11,k2_zfmisc_1(X12,X13))
      | k1_mcart_1(X11) = sK12(X11) ) ),
    inference(superposition,[],[f72,f87])).

fof(f679,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl14_27 ),
    inference(avatar_component_clause,[],[f677])).

fof(f1144,plain,
    ( ~ spl14_19
    | ~ spl14_27 ),
    inference(avatar_contradiction_clause,[],[f1143])).

fof(f1143,plain,
    ( $false
    | ~ spl14_19
    | ~ spl14_27 ),
    inference(subsumption_resolution,[],[f679,f639])).

fof(f639,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK6,k2_zfmisc_1(X0,X1))
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f638])).

fof(f1102,plain,
    ( spl14_1
    | spl14_27 ),
    inference(avatar_split_clause,[],[f1093,f677,f117])).

fof(f1093,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(resolution,[],[f96,f74])).

fof(f1078,plain,(
    ~ spl14_1 ),
    inference(avatar_contradiction_clause,[],[f1077])).

fof(f1077,plain,
    ( $false
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f1076,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f1076,plain,
    ( k1_xboole_0 = sK3
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f1075,f56])).

fof(f56,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f1075,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f1060,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1060,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ spl14_1 ),
    inference(superposition,[],[f922,f1035])).

fof(f1035,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f1012,f58])).

fof(f58,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f1012,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 = sK4
    | ~ spl14_1 ),
    inference(resolution,[],[f922,f118])).

fof(f118,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f922,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f921])).

fof(f921,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f900,f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f107,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f146,f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f68,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK10(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK11(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( sP0(sK11(X0),X0)
        & r2_hidden(sK11(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f29,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK11(X0),X0)
        & r2_hidden(sK11(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f22,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f146,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3),k1_xboole_0) ),
    inference(superposition,[],[f105,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f93,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f88,f80])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f107,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f91,f94])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f900,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(condensation,[],[f874])).

fof(f874,plain,(
    ! [X14,X15,X13,X16] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X13,X14),X16)
      | k1_xboole_0 = X16
      | k1_xboole_0 = X15
      | k1_xboole_0 = X14
      | k1_xboole_0 = X13
      | ~ v1_xboole_0(k2_zfmisc_1(X13,X14)) ) ),
    inference(superposition,[],[f102,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f180,f111])).

fof(f180,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f106,f105])).

fof(f106,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f92,f94])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f804,plain,(
    spl14_17 ),
    inference(avatar_split_clause,[],[f803,f600])).

fof(f600,plain,
    ( spl14_17
  <=> sP1(sK6,sK4,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f803,plain,(
    sP1(sK6,sK4,sK3,sK2) ),
    inference(subsumption_resolution,[],[f802,f56])).

fof(f802,plain,
    ( sP1(sK6,sK4,sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f801,f57])).

fof(f801,plain,
    ( sP1(sK6,sK4,sK3,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f767,f58])).

fof(f767,plain,
    ( sP1(sK6,sK4,sK3,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f97,f96])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP1(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f86,f80])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f26,f30])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP1(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f607,plain,
    ( ~ spl14_17
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f598,f604,f600])).

fof(f598,plain,
    ( sK5 != k2_mcart_1(sK6)
    | ~ sP1(sK6,sK4,sK3,sK2) ),
    inference(superposition,[],[f59,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP1(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.35/0.54  % (12237)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.55  % (12235)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.55  % (12253)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.56  % (12257)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.56  % (12252)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.57  % (12261)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.57  % (12243)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.57  % (12262)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.57  % (12236)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.57  % (12248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.57  % (12249)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.57  % (12244)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.57  % (12240)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.57  % (12238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.57  % (12252)Refutation not found, incomplete strategy% (12252)------------------------------
% 1.35/0.57  % (12252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (12252)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (12252)Memory used [KB]: 10618
% 1.35/0.57  % (12252)Time elapsed: 0.075 s
% 1.35/0.57  % (12252)------------------------------
% 1.35/0.57  % (12252)------------------------------
% 1.35/0.58  % (12244)Refutation not found, incomplete strategy% (12244)------------------------------
% 1.35/0.58  % (12244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (12236)Refutation not found, incomplete strategy% (12236)------------------------------
% 1.35/0.58  % (12236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (12244)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.58  
% 1.35/0.58  % (12244)Memory used [KB]: 10618
% 1.35/0.58  % (12244)Time elapsed: 0.084 s
% 1.35/0.58  % (12244)------------------------------
% 1.35/0.58  % (12244)------------------------------
% 1.35/0.58  % (12245)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.58  % (12250)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.58  % (12257)Refutation not found, incomplete strategy% (12257)------------------------------
% 1.35/0.58  % (12257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (12257)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.58  
% 1.35/0.58  % (12257)Memory used [KB]: 1791
% 1.35/0.58  % (12257)Time elapsed: 0.156 s
% 1.35/0.58  % (12257)------------------------------
% 1.35/0.58  % (12257)------------------------------
% 1.35/0.59  % (12260)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.59  % (12259)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.59  % (12242)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.59  % (12258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.60  % (12243)Refutation not found, incomplete strategy% (12243)------------------------------
% 1.35/0.60  % (12243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.60  % (12236)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.60  
% 1.35/0.60  % (12236)Memory used [KB]: 10874
% 1.35/0.60  % (12236)Time elapsed: 0.135 s
% 1.35/0.60  % (12236)------------------------------
% 1.35/0.60  % (12236)------------------------------
% 1.35/0.60  % (12264)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.60  % (12246)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.60  % (12243)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.60  
% 1.35/0.60  % (12243)Memory used [KB]: 10874
% 1.35/0.60  % (12243)Time elapsed: 0.153 s
% 1.35/0.60  % (12243)------------------------------
% 1.35/0.60  % (12243)------------------------------
% 1.35/0.60  % (12241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.60  % (12255)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.61  % (12239)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.61  % (12263)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.62  % (12247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.62  % (12258)Refutation not found, incomplete strategy% (12258)------------------------------
% 1.35/0.62  % (12258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.62  % (12258)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.62  
% 1.35/0.62  % (12258)Memory used [KB]: 11001
% 1.35/0.62  % (12258)Time elapsed: 0.183 s
% 1.35/0.62  % (12258)------------------------------
% 1.35/0.62  % (12258)------------------------------
% 2.05/0.62  % (12234)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.05/0.63  % (12265)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.05/0.64  % (12256)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.05/0.64  % (12256)Refutation not found, incomplete strategy% (12256)------------------------------
% 2.05/0.64  % (12256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (12256)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.64  
% 2.05/0.64  % (12256)Memory used [KB]: 10746
% 2.05/0.64  % (12256)Time elapsed: 0.209 s
% 2.05/0.64  % (12256)------------------------------
% 2.05/0.64  % (12256)------------------------------
% 2.05/0.66  % (12263)Refutation found. Thanks to Tanya!
% 2.05/0.66  % SZS status Theorem for theBenchmark
% 2.05/0.66  % SZS output start Proof for theBenchmark
% 2.05/0.66  fof(f1291,plain,(
% 2.05/0.66    $false),
% 2.05/0.66    inference(avatar_sat_refutation,[],[f607,f804,f1078,f1102,f1144,f1168,f1210,f1232,f1266,f1274,f1277,f1286,f1290])).
% 2.05/0.66  fof(f1290,plain,(
% 2.05/0.66    spl14_1 | spl14_41),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f1289])).
% 2.05/0.66  fof(f1289,plain,(
% 2.05/0.66    $false | (spl14_1 | spl14_41)),
% 2.05/0.66    inference(subsumption_resolution,[],[f1288,f138])).
% 2.05/0.66  fof(f138,plain,(
% 2.05/0.66    r2_hidden(k2_mcart_1(sK6),sK4) | spl14_1),
% 2.05/0.66    inference(resolution,[],[f82,f130])).
% 2.05/0.66  fof(f130,plain,(
% 2.05/0.66    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | spl14_1),
% 2.05/0.66    inference(subsumption_resolution,[],[f127,f119])).
% 2.05/0.66  fof(f119,plain,(
% 2.05/0.66    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | spl14_1),
% 2.05/0.66    inference(avatar_component_clause,[],[f117])).
% 2.05/0.66  fof(f117,plain,(
% 2.05/0.66    spl14_1 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 2.05/0.66  fof(f127,plain,(
% 2.05/0.66    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.05/0.66    inference(resolution,[],[f74,f96])).
% 2.05/0.66  fof(f96,plain,(
% 2.05/0.66    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.05/0.66    inference(definition_unfolding,[],[f54,f80])).
% 2.05/0.66  fof(f80,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f10])).
% 2.05/0.66  fof(f10,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.05/0.66  fof(f54,plain,(
% 2.05/0.66    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.05/0.66    inference(cnf_transformation,[],[f33])).
% 2.05/0.66  fof(f33,plain,(
% 2.05/0.66    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f32])).
% 2.05/0.66  fof(f32,plain,(
% 2.05/0.66    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK5 != k7_mcart_1(sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f20,plain,(
% 2.05/0.66    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.05/0.66    inference(flattening,[],[f19])).
% 2.05/0.66  fof(f19,plain,(
% 2.05/0.66    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.05/0.66    inference(ennf_transformation,[],[f18])).
% 2.05/0.66  fof(f18,negated_conjecture,(
% 2.05/0.66    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.05/0.66    inference(negated_conjecture,[],[f17])).
% 2.05/0.66  fof(f17,conjecture,(
% 2.05/0.66    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 2.05/0.66  fof(f74,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f47])).
% 2.05/0.66  fof(f47,plain,(
% 2.05/0.66    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.05/0.66    inference(nnf_transformation,[],[f23])).
% 2.05/0.66  fof(f23,plain,(
% 2.05/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f5])).
% 2.05/0.66  fof(f5,axiom,(
% 2.05/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.05/0.66  fof(f82,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f25])).
% 2.05/0.66  fof(f25,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.05/0.66    inference(ennf_transformation,[],[f12])).
% 2.05/0.66  fof(f12,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.05/0.66  fof(f1288,plain,(
% 2.05/0.66    ~r2_hidden(k2_mcart_1(sK6),sK4) | spl14_41),
% 2.05/0.66    inference(resolution,[],[f1265,f78])).
% 2.05/0.66  fof(f78,plain,(
% 2.05/0.66    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f24])).
% 2.05/0.66  fof(f24,plain,(
% 2.05/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f6])).
% 2.05/0.66  fof(f6,axiom,(
% 2.05/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 2.05/0.66  fof(f1265,plain,(
% 2.05/0.66    ~m1_subset_1(k2_mcart_1(sK6),sK4) | spl14_41),
% 2.05/0.66    inference(avatar_component_clause,[],[f1263])).
% 2.05/0.66  fof(f1263,plain,(
% 2.05/0.66    spl14_41 <=> m1_subset_1(k2_mcart_1(sK6),sK4)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_41])])).
% 2.05/0.66  fof(f1286,plain,(
% 2.05/0.66    spl14_38 | ~spl14_36 | spl14_40),
% 2.05/0.66    inference(avatar_split_clause,[],[f1285,f1259,f1220,f1252])).
% 2.05/0.66  fof(f1252,plain,(
% 2.05/0.66    spl14_38 <=> ! [X0] : (~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).
% 2.05/0.66  fof(f1220,plain,(
% 2.05/0.66    spl14_36 <=> m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).
% 2.05/0.66  fof(f1259,plain,(
% 2.05/0.66    spl14_40 <=> m1_subset_1(sK9(k1_mcart_1(sK6)),sK3)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).
% 2.05/0.66  fof(f1285,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | (~spl14_36 | spl14_40)),
% 2.05/0.66    inference(subsumption_resolution,[],[f1284,f1221])).
% 2.05/0.66  fof(f1221,plain,(
% 2.05/0.66    m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl14_36),
% 2.05/0.66    inference(avatar_component_clause,[],[f1220])).
% 2.05/0.66  fof(f1284,plain,(
% 2.05/0.66    ( ! [X0] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | ~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | spl14_40),
% 2.05/0.66    inference(superposition,[],[f1261,f468])).
% 2.05/0.66  fof(f468,plain,(
% 2.05/0.66    ( ! [X6,X7] : (sK9(X6) = k2_mcart_1(X6) | ~r2_hidden(X6,X7) | ~v1_relat_1(X7)) )),
% 2.05/0.66    inference(superposition,[],[f73,f61])).
% 2.05/0.66  fof(f61,plain,(
% 2.05/0.66    ( ! [X4,X0] : (k4_tarski(sK8(X4),sK9(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f38])).
% 2.05/0.66  fof(f38,plain,(
% 2.05/0.66    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK7(X0) & r2_hidden(sK7(X0),X0))) & (! [X4] : (k4_tarski(sK8(X4),sK9(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f37,f36])).
% 2.05/0.66  fof(f36,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK7(X0) & r2_hidden(sK7(X0),X0)))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f37,plain,(
% 2.05/0.66    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK8(X4),sK9(X4)) = X4)),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 2.05/0.66    inference(rectify,[],[f34])).
% 2.05/0.66  fof(f34,plain,(
% 2.05/0.66    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 2.05/0.66    inference(nnf_transformation,[],[f21])).
% 2.05/0.66  fof(f21,plain,(
% 2.05/0.66    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f7])).
% 2.05/0.66  fof(f7,axiom,(
% 2.05/0.66    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 2.05/0.66  fof(f73,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f16])).
% 2.05/0.66  fof(f16,axiom,(
% 2.05/0.66    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.05/0.66  fof(f1261,plain,(
% 2.05/0.66    ~m1_subset_1(sK9(k1_mcart_1(sK6)),sK3) | spl14_40),
% 2.05/0.66    inference(avatar_component_clause,[],[f1259])).
% 2.05/0.66  fof(f1277,plain,(
% 2.05/0.66    spl14_1 | ~spl14_38),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f1276])).
% 2.05/0.66  fof(f1276,plain,(
% 2.05/0.66    $false | (spl14_1 | ~spl14_38)),
% 2.05/0.66    inference(subsumption_resolution,[],[f1275,f71])).
% 2.05/0.66  fof(f71,plain,(
% 2.05/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f8])).
% 2.05/0.66  fof(f8,axiom,(
% 2.05/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.05/0.66  fof(f1275,plain,(
% 2.05/0.66    ~v1_relat_1(k2_zfmisc_1(sK2,sK3)) | (spl14_1 | ~spl14_38)),
% 2.05/0.66    inference(resolution,[],[f1253,f132])).
% 2.05/0.66  fof(f132,plain,(
% 2.05/0.66    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) | spl14_1),
% 2.05/0.66    inference(resolution,[],[f81,f130])).
% 2.05/0.66  fof(f81,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f25])).
% 2.05/0.66  fof(f1253,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | ~spl14_38),
% 2.05/0.66    inference(avatar_component_clause,[],[f1252])).
% 2.05/0.66  fof(f1274,plain,(
% 2.05/0.66    spl14_38 | spl14_1 | spl14_39),
% 2.05/0.66    inference(avatar_split_clause,[],[f1273,f1255,f117,f1252])).
% 2.05/0.66  fof(f1255,plain,(
% 2.05/0.66    spl14_39 <=> m1_subset_1(sK8(k1_mcart_1(sK6)),sK2)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_39])])).
% 2.05/0.66  fof(f1273,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | (spl14_1 | spl14_39)),
% 2.05/0.66    inference(subsumption_resolution,[],[f1272,f136])).
% 2.05/0.66  fof(f136,plain,(
% 2.05/0.66    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) | spl14_1),
% 2.05/0.66    inference(resolution,[],[f132,f81])).
% 2.05/0.66  fof(f1272,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) | ~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | spl14_39),
% 2.05/0.66    inference(superposition,[],[f1268,f469])).
% 2.05/0.66  fof(f469,plain,(
% 2.05/0.66    ( ! [X8,X9] : (sK8(X8) = k1_mcart_1(X8) | ~r2_hidden(X8,X9) | ~v1_relat_1(X9)) )),
% 2.05/0.66    inference(superposition,[],[f72,f61])).
% 2.05/0.66  fof(f72,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f16])).
% 2.05/0.66  fof(f1268,plain,(
% 2.05/0.66    ~r2_hidden(sK8(k1_mcart_1(sK6)),sK2) | spl14_39),
% 2.05/0.66    inference(resolution,[],[f1257,f78])).
% 2.05/0.66  fof(f1257,plain,(
% 2.05/0.66    ~m1_subset_1(sK8(k1_mcart_1(sK6)),sK2) | spl14_39),
% 2.05/0.66    inference(avatar_component_clause,[],[f1255])).
% 2.05/0.66  fof(f1266,plain,(
% 2.05/0.66    spl14_38 | ~spl14_39 | ~spl14_40 | ~spl14_41 | spl14_18 | ~spl14_32),
% 2.05/0.66    inference(avatar_split_clause,[],[f1250,f1165,f604,f1263,f1259,f1255,f1252])).
% 2.05/0.66  fof(f604,plain,(
% 2.05/0.66    spl14_18 <=> sK5 = k2_mcart_1(sK6)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 2.05/0.66  fof(f1165,plain,(
% 2.05/0.66    spl14_32 <=> sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).
% 2.05/0.66  fof(f1250,plain,(
% 2.05/0.66    ( ! [X0] : (~m1_subset_1(k2_mcart_1(sK6),sK4) | ~m1_subset_1(sK9(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK8(k1_mcart_1(sK6)),sK2) | ~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | (spl14_18 | ~spl14_32)),
% 2.05/0.66    inference(subsumption_resolution,[],[f1249,f606])).
% 2.05/0.66  fof(f606,plain,(
% 2.05/0.66    sK5 != k2_mcart_1(sK6) | spl14_18),
% 2.05/0.66    inference(avatar_component_clause,[],[f604])).
% 2.05/0.66  fof(f1249,plain,(
% 2.05/0.66    ( ! [X0] : (sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | ~m1_subset_1(sK9(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK8(k1_mcart_1(sK6)),sK2) | ~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | ~spl14_32),
% 2.05/0.66    inference(trivial_inequality_removal,[],[f1245])).
% 2.05/0.66  fof(f1245,plain,(
% 2.05/0.66    ( ! [X0] : (sK6 != sK6 | sK5 = k2_mcart_1(sK6) | ~m1_subset_1(k2_mcart_1(sK6),sK4) | ~m1_subset_1(sK9(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK8(k1_mcart_1(sK6)),sK2) | ~r2_hidden(k1_mcart_1(sK6),X0) | ~v1_relat_1(X0)) ) | ~spl14_32),
% 2.05/0.66    inference(superposition,[],[f467,f1167])).
% 2.05/0.66  fof(f1167,plain,(
% 2.05/0.66    sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) | ~spl14_32),
% 2.05/0.66    inference(avatar_component_clause,[],[f1165])).
% 2.05/0.66  fof(f467,plain,(
% 2.05/0.66    ( ! [X4,X5,X3] : (k4_tarski(X3,X4) != sK6 | sK5 = X4 | ~m1_subset_1(X4,sK4) | ~m1_subset_1(sK9(X3),sK3) | ~m1_subset_1(sK8(X3),sK2) | ~r2_hidden(X3,X5) | ~v1_relat_1(X5)) )),
% 2.05/0.66    inference(superposition,[],[f95,f61])).
% 2.05/0.66  fof(f95,plain,(
% 2.05/0.66    ( ! [X6,X7,X5] : (sK6 != k4_tarski(k4_tarski(X5,X6),X7) | sK5 = X7 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f55,f79])).
% 2.05/0.66  fof(f79,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f9])).
% 2.05/0.66  fof(f9,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.05/0.66  fof(f55,plain,(
% 2.05/0.66    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f33])).
% 2.05/0.66  fof(f1232,plain,(
% 2.05/0.66    spl14_36 | spl14_1 | ~spl14_15),
% 2.05/0.66    inference(avatar_split_clause,[],[f1231,f591,f117,f1220])).
% 2.05/0.66  fof(f591,plain,(
% 2.05/0.66    spl14_15 <=> m1_subset_1(sK13(k1_mcart_1(sK6)),sK3)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).
% 2.05/0.66  fof(f1231,plain,(
% 2.05/0.66    m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) | (spl14_1 | ~spl14_15)),
% 2.05/0.66    inference(forward_demodulation,[],[f592,f1133])).
% 2.05/0.66  fof(f1133,plain,(
% 2.05/0.66    k2_mcart_1(k1_mcart_1(sK6)) = sK13(k1_mcart_1(sK6)) | spl14_1),
% 2.05/0.66    inference(resolution,[],[f132,f513])).
% 2.05/0.66  fof(f513,plain,(
% 2.05/0.66    ( ! [X10,X8,X9] : (~r2_hidden(X8,k2_zfmisc_1(X9,X10)) | k2_mcart_1(X8) = sK13(X8)) )),
% 2.05/0.66    inference(superposition,[],[f73,f87])).
% 2.05/0.66  fof(f87,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k4_tarski(sK12(X0),sK13(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f51])).
% 2.05/0.66  fof(f51,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (k4_tarski(sK12(X0),sK13(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f27,f50])).
% 2.05/0.66  fof(f50,plain,(
% 2.05/0.66    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK12(X0),sK13(X0)) = X0)),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f27,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.05/0.66    inference(ennf_transformation,[],[f4])).
% 2.05/0.66  fof(f4,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.05/0.66  fof(f592,plain,(
% 2.05/0.66    m1_subset_1(sK13(k1_mcart_1(sK6)),sK3) | ~spl14_15),
% 2.05/0.66    inference(avatar_component_clause,[],[f591])).
% 2.05/0.66  fof(f1210,plain,(
% 2.05/0.66    spl14_1 | spl14_15),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f1209])).
% 2.05/0.66  fof(f1209,plain,(
% 2.05/0.66    $false | (spl14_1 | spl14_15)),
% 2.05/0.66    inference(subsumption_resolution,[],[f1206,f139])).
% 2.05/0.66  fof(f139,plain,(
% 2.05/0.66    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) | spl14_1),
% 2.05/0.66    inference(resolution,[],[f82,f132])).
% 2.05/0.66  fof(f1206,plain,(
% 2.05/0.66    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) | (spl14_1 | spl14_15)),
% 2.05/0.66    inference(backward_demodulation,[],[f611,f1133])).
% 2.05/0.66  fof(f611,plain,(
% 2.05/0.66    ~r2_hidden(sK13(k1_mcart_1(sK6)),sK3) | spl14_15),
% 2.05/0.66    inference(resolution,[],[f593,f78])).
% 2.05/0.66  fof(f593,plain,(
% 2.05/0.66    ~m1_subset_1(sK13(k1_mcart_1(sK6)),sK3) | spl14_15),
% 2.05/0.66    inference(avatar_component_clause,[],[f591])).
% 2.05/0.66  fof(f1168,plain,(
% 2.05/0.66    spl14_19 | spl14_32 | spl14_1 | ~spl14_27),
% 2.05/0.66    inference(avatar_split_clause,[],[f1163,f677,f117,f1165,f638])).
% 2.05/0.66  fof(f638,plain,(
% 2.05/0.66    spl14_19 <=> ! [X1,X0] : ~r2_hidden(sK6,k2_zfmisc_1(X0,X1))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 2.05/0.66  fof(f677,plain,(
% 2.05/0.66    spl14_27 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).
% 2.05/0.66  fof(f1163,plain,(
% 2.05/0.66    ( ! [X0,X1] : (sK6 = k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) | ~r2_hidden(sK6,k2_zfmisc_1(X0,X1))) ) | (spl14_1 | ~spl14_27)),
% 2.05/0.66    inference(forward_demodulation,[],[f1162,f618])).
% 2.05/0.66  fof(f618,plain,(
% 2.05/0.66    k2_mcart_1(sK6) = sK13(sK6) | spl14_1),
% 2.05/0.66    inference(resolution,[],[f513,f130])).
% 2.05/0.66  fof(f1162,plain,(
% 2.05/0.66    ( ! [X0,X1] : (sK6 = k4_tarski(k1_mcart_1(sK6),sK13(sK6)) | ~r2_hidden(sK6,k2_zfmisc_1(X0,X1))) ) | ~spl14_27),
% 2.05/0.66    inference(superposition,[],[f87,f1145])).
% 2.05/0.66  fof(f1145,plain,(
% 2.05/0.66    k1_mcart_1(sK6) = sK12(sK6) | ~spl14_27),
% 2.05/0.66    inference(resolution,[],[f679,f514])).
% 2.05/0.66  fof(f514,plain,(
% 2.05/0.66    ( ! [X12,X13,X11] : (~r2_hidden(X11,k2_zfmisc_1(X12,X13)) | k1_mcart_1(X11) = sK12(X11)) )),
% 2.05/0.66    inference(superposition,[],[f72,f87])).
% 2.05/0.66  fof(f679,plain,(
% 2.05/0.66    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl14_27),
% 2.05/0.66    inference(avatar_component_clause,[],[f677])).
% 2.05/0.66  fof(f1144,plain,(
% 2.05/0.66    ~spl14_19 | ~spl14_27),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f1143])).
% 2.05/0.66  fof(f1143,plain,(
% 2.05/0.66    $false | (~spl14_19 | ~spl14_27)),
% 2.05/0.66    inference(subsumption_resolution,[],[f679,f639])).
% 2.05/0.66  fof(f639,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r2_hidden(sK6,k2_zfmisc_1(X0,X1))) ) | ~spl14_19),
% 2.05/0.66    inference(avatar_component_clause,[],[f638])).
% 2.05/0.66  fof(f1102,plain,(
% 2.05/0.66    spl14_1 | spl14_27),
% 2.05/0.66    inference(avatar_split_clause,[],[f1093,f677,f117])).
% 2.05/0.66  fof(f1093,plain,(
% 2.05/0.66    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.05/0.66    inference(resolution,[],[f96,f74])).
% 2.05/0.66  fof(f1078,plain,(
% 2.05/0.66    ~spl14_1),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f1077])).
% 2.05/0.66  fof(f1077,plain,(
% 2.05/0.66    $false | ~spl14_1),
% 2.05/0.66    inference(subsumption_resolution,[],[f1076,f57])).
% 2.05/0.66  fof(f57,plain,(
% 2.05/0.66    k1_xboole_0 != sK3),
% 2.05/0.66    inference(cnf_transformation,[],[f33])).
% 2.05/0.66  fof(f1076,plain,(
% 2.05/0.66    k1_xboole_0 = sK3 | ~spl14_1),
% 2.05/0.66    inference(subsumption_resolution,[],[f1075,f56])).
% 2.05/0.66  fof(f56,plain,(
% 2.05/0.66    k1_xboole_0 != sK2),
% 2.05/0.66    inference(cnf_transformation,[],[f33])).
% 2.05/0.66  fof(f1075,plain,(
% 2.05/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl14_1),
% 2.05/0.66    inference(subsumption_resolution,[],[f1060,f60])).
% 2.05/0.66  fof(f60,plain,(
% 2.05/0.66    v1_xboole_0(k1_xboole_0)),
% 2.05/0.66    inference(cnf_transformation,[],[f2])).
% 2.05/0.66  fof(f2,axiom,(
% 2.05/0.66    v1_xboole_0(k1_xboole_0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.05/0.66  fof(f1060,plain,(
% 2.05/0.66    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~spl14_1),
% 2.05/0.66    inference(superposition,[],[f922,f1035])).
% 2.05/0.66  fof(f1035,plain,(
% 2.05/0.66    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl14_1),
% 2.05/0.66    inference(subsumption_resolution,[],[f1012,f58])).
% 2.05/0.66  fof(f58,plain,(
% 2.05/0.66    k1_xboole_0 != sK4),
% 2.05/0.66    inference(cnf_transformation,[],[f33])).
% 2.05/0.66  fof(f1012,plain,(
% 2.05/0.66    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | k1_xboole_0 = sK4 | ~spl14_1),
% 2.05/0.66    inference(resolution,[],[f922,f118])).
% 2.05/0.66  fof(f118,plain,(
% 2.05/0.66    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~spl14_1),
% 2.05/0.66    inference(avatar_component_clause,[],[f117])).
% 2.05/0.66  fof(f922,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(condensation,[],[f921])).
% 2.05/0.66  fof(f921,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 2.05/0.66    inference(subsumption_resolution,[],[f900,f304])).
% 2.05/0.66  fof(f304,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.05/0.66    inference(superposition,[],[f107,f159])).
% 2.05/0.66  fof(f159,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0) = X0 | ~v1_xboole_0(X0)) )),
% 2.05/0.66    inference(superposition,[],[f146,f111])).
% 2.05/0.66  fof(f111,plain,(
% 2.05/0.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.05/0.66    inference(resolution,[],[f68,f64])).
% 2.05/0.66  fof(f64,plain,(
% 2.05/0.66    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f42])).
% 2.05/0.66  fof(f42,plain,(
% 2.05/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK10(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f40,f41])).
% 2.05/0.66  fof(f41,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f40,plain,(
% 2.05/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.05/0.66    inference(rectify,[],[f39])).
% 2.05/0.66  fof(f39,plain,(
% 2.05/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.05/0.66    inference(nnf_transformation,[],[f1])).
% 2.05/0.66  fof(f1,axiom,(
% 2.05/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.05/0.66  fof(f68,plain,(
% 2.05/0.66    ( ! [X0] : (r2_hidden(sK11(X0),X0) | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f46])).
% 2.05/0.66  fof(f46,plain,(
% 2.05/0.66    ! [X0] : ((sP0(sK11(X0),X0) & r2_hidden(sK11(X0),X0)) | k1_xboole_0 = X0)),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f29,f45])).
% 2.05/0.66  fof(f45,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK11(X0),X0) & r2_hidden(sK11(X0),X0)))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f29,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.05/0.66    inference(definition_folding,[],[f22,f28])).
% 2.05/0.66  fof(f28,plain,(
% 2.05/0.66    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 2.05/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.05/0.66  fof(f22,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.05/0.66    inference(ennf_transformation,[],[f13])).
% 2.05/0.66  fof(f13,axiom,(
% 2.05/0.66    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 2.05/0.66  fof(f146,plain,(
% 2.05/0.66    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3),k1_xboole_0)) )),
% 2.05/0.66    inference(superposition,[],[f105,f105])).
% 2.05/0.66  fof(f105,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.05/0.66    inference(equality_resolution,[],[f98])).
% 2.05/0.66  fof(f98,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f93,f94])).
% 2.05/0.66  fof(f94,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f88,f80])).
% 2.05/0.66  fof(f88,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f11])).
% 2.05/0.66  fof(f11,axiom,(
% 2.05/0.66    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.05/0.66  fof(f93,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f53])).
% 2.05/0.66  fof(f53,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.05/0.66    inference(flattening,[],[f52])).
% 2.05/0.66  fof(f52,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.05/0.66    inference(nnf_transformation,[],[f15])).
% 2.05/0.66  fof(f15,axiom,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.05/0.66  fof(f107,plain,(
% 2.05/0.66    ( ! [X2,X0,X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3)) )),
% 2.05/0.66    inference(equality_resolution,[],[f100])).
% 2.05/0.66  fof(f100,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f91,f94])).
% 2.05/0.66  fof(f91,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f53])).
% 2.05/0.66  fof(f900,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 2.05/0.66    inference(condensation,[],[f874])).
% 2.05/0.66  fof(f874,plain,(
% 2.05/0.66    ( ! [X14,X15,X13,X16] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X13,X14),X16) | k1_xboole_0 = X16 | k1_xboole_0 = X15 | k1_xboole_0 = X14 | k1_xboole_0 = X13 | ~v1_xboole_0(k2_zfmisc_1(X13,X14))) )),
% 2.05/0.66    inference(superposition,[],[f102,f195])).
% 2.05/0.66  fof(f195,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 2.05/0.66    inference(superposition,[],[f180,f111])).
% 2.05/0.66  fof(f180,plain,(
% 2.05/0.66    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 2.05/0.66    inference(superposition,[],[f106,f105])).
% 2.05/0.66  fof(f106,plain,(
% 2.05/0.66    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.05/0.66    inference(equality_resolution,[],[f99])).
% 2.05/0.66  fof(f99,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f92,f94])).
% 2.05/0.66  fof(f92,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f53])).
% 2.05/0.66  fof(f102,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(definition_unfolding,[],[f89,f94])).
% 2.05/0.66  fof(f89,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f53])).
% 2.05/0.66  fof(f804,plain,(
% 2.05/0.66    spl14_17),
% 2.05/0.66    inference(avatar_split_clause,[],[f803,f600])).
% 2.05/0.66  fof(f600,plain,(
% 2.05/0.66    spl14_17 <=> sP1(sK6,sK4,sK3,sK2)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 2.05/0.66  fof(f803,plain,(
% 2.05/0.66    sP1(sK6,sK4,sK3,sK2)),
% 2.05/0.66    inference(subsumption_resolution,[],[f802,f56])).
% 2.05/0.66  fof(f802,plain,(
% 2.05/0.66    sP1(sK6,sK4,sK3,sK2) | k1_xboole_0 = sK2),
% 2.05/0.66    inference(subsumption_resolution,[],[f801,f57])).
% 2.05/0.66  fof(f801,plain,(
% 2.05/0.66    sP1(sK6,sK4,sK3,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 2.05/0.66    inference(subsumption_resolution,[],[f767,f58])).
% 2.05/0.66  fof(f767,plain,(
% 2.05/0.66    sP1(sK6,sK4,sK3,sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 2.05/0.66    inference(resolution,[],[f97,f96])).
% 2.05/0.66  fof(f97,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP1(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(definition_unfolding,[],[f86,f80])).
% 2.05/0.66  fof(f86,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (sP1(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f31])).
% 2.05/0.66  fof(f31,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (! [X3] : (sP1(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.05/0.66    inference(definition_folding,[],[f26,f30])).
% 2.05/0.66  fof(f30,plain,(
% 2.05/0.66    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP1(X3,X2,X1,X0))),
% 2.05/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.05/0.66  fof(f26,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.05/0.66    inference(ennf_transformation,[],[f14])).
% 2.05/0.66  fof(f14,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.05/0.66  fof(f607,plain,(
% 2.05/0.66    ~spl14_17 | ~spl14_18),
% 2.05/0.66    inference(avatar_split_clause,[],[f598,f604,f600])).
% 2.05/0.66  fof(f598,plain,(
% 2.05/0.66    sK5 != k2_mcart_1(sK6) | ~sP1(sK6,sK4,sK3,sK2)),
% 2.05/0.66    inference(superposition,[],[f59,f85])).
% 2.05/0.66  fof(f85,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f49])).
% 2.05/0.66  fof(f49,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP1(X0,X1,X2,X3))),
% 2.05/0.66    inference(rectify,[],[f48])).
% 2.05/0.66  fof(f48,plain,(
% 2.05/0.66    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP1(X3,X2,X1,X0))),
% 2.05/0.66    inference(nnf_transformation,[],[f30])).
% 2.05/0.66  fof(f59,plain,(
% 2.05/0.66    sK5 != k7_mcart_1(sK2,sK3,sK4,sK6)),
% 2.05/0.66    inference(cnf_transformation,[],[f33])).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (12263)------------------------------
% 2.05/0.66  % (12263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (12263)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (12263)Memory used [KB]: 6908
% 2.05/0.66  % (12263)Time elapsed: 0.224 s
% 2.05/0.66  % (12263)------------------------------
% 2.05/0.66  % (12263)------------------------------
% 2.05/0.68  % (12226)Success in time 0.322 s
%------------------------------------------------------------------------------
