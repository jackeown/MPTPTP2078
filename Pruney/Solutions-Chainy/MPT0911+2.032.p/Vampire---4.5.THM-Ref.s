%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 213 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  359 ( 715 expanded)
%              Number of equality atoms :   87 ( 228 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f88,f98,f108,f110,f113,f115,f122,f127,f132,f139,f144,f160,f163,f167,f170])).

fof(f170,plain,
    ( ~ spl5_6
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f34,f83,f156])).

fof(f156,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_18
  <=> ! [X1] :
        ( ~ r2_hidden(sK4,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f83,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_6
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f167,plain,
    ( ~ spl5_14
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f34,f131,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK4),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK4),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f131,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_14
  <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f163,plain,
    ( ~ spl5_13
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl5_13
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f126,f153,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f153,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_17
  <=> m1_subset_1(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f126,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_13
  <=> r2_hidden(k2_mcart_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f160,plain,
    ( ~ spl5_15
    | ~ spl5_17
    | spl5_18
    | spl5_19
    | spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f149,f141,f119,f158,f155,f151,f136])).

fof(f136,plain,
    ( spl5_15
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f119,plain,
    ( spl5_12
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f141,plain,
    ( spl5_16
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( sK3 = k2_mcart_1(sK4)
        | ~ r2_hidden(k1_mcart_1(sK4),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK4,X1)
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl5_16 ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( sK4 != sK4
        | sK3 = k2_mcart_1(sK4)
        | ~ r2_hidden(k1_mcart_1(sK4),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK4,X1)
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl5_16 ),
    inference(resolution,[],[f147,f143])).

fof(f143,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK1)
      | sK4 != X0
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK0) ) ),
    inference(resolution,[],[f146,f36])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | sK4 != X0
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK1) ) ),
    inference(resolution,[],[f145,f36])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK1)
      | sK4 != X0
      | ~ m1_subset_1(k2_mcart_1(X0),sK2)
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f111,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | sK3 = X1
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f48,f35])).

fof(f48,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X7 ) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f27,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f144,plain,
    ( spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f134,f129,f141])).

fof(f134,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f131,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f139,plain,
    ( spl5_15
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f133,f129,f136])).

fof(f133,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f131,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f132,plain,
    ( spl5_14
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f116,f81,f129])).

fof(f116,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_6 ),
    inference(resolution,[],[f83,f41])).

fof(f127,plain,
    ( spl5_13
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f117,f81,f124])).

fof(f117,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f83,f42])).

fof(f122,plain,
    ( spl5_1
    | ~ spl5_5
    | spl5_3
    | spl5_2
    | ~ spl5_12
    | spl5_4 ),
    inference(avatar_split_clause,[],[f78,f69,f119,f59,f64,f74,f54])).

fof(f54,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f64,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f59,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f69,plain,
    ( spl5_4
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | spl5_4 ),
    inference(superposition,[],[f71,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f71,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f115,plain,
    ( spl5_2
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl5_2
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f61,f107,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f107,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f61,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f113,plain,
    ( spl5_1
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl5_1
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f56,f103,f33])).

fof(f103,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f56,plain,
    ( k1_xboole_0 != sK0
    | spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f110,plain,
    ( spl5_3
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl5_3
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f66,f97,f33])).

fof(f97,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f66,plain,
    ( k1_xboole_0 != sK2
    | spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f108,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f99,f91,f105,f101])).

fof(f91,plain,
    ( spl5_8
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f99,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f93,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f98,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f89,f85,f95,f91])).

fof(f85,plain,
    ( spl5_7
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f89,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f87,f38])).

fof(f87,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f88,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f79,f74,f85,f81])).

fof(f79,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f76,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f47,f74])).

fof(f47,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f28,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (17069)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (17061)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (17053)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (17050)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (17051)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (17069)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f88,f98,f108,f110,f113,f115,f122,f127,f132,f139,f144,f160,f163,f167,f170])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ~spl5_6 | ~spl5_18),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    $false | (~spl5_6 | ~spl5_18)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f34,f83,f156])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(sK4,X1) | ~v1_relat_1(X1)) ) | ~spl5_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl5_18 <=> ! [X1] : (~r2_hidden(sK4,X1) | ~v1_relat_1(X1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl5_6 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ~spl5_14 | ~spl5_19),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    $false | (~spl5_14 | ~spl5_19)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f34,f131,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),X0) | ~v1_relat_1(X0)) ) | ~spl5_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f158])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl5_19 <=> ! [X0] : (~r2_hidden(k1_mcart_1(sK4),X0) | ~v1_relat_1(X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl5_14 <=> r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ~spl5_13 | spl5_17),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f161])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    $false | (~spl5_13 | spl5_17)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f126,f153,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ~m1_subset_1(k2_mcart_1(sK4),sK2) | spl5_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl5_17 <=> m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl5_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f124])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl5_13 <=> r2_hidden(k2_mcart_1(sK4),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    ~spl5_15 | ~spl5_17 | spl5_18 | spl5_19 | spl5_12 | ~spl5_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f149,f141,f119,f158,f155,f151,f136])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    spl5_15 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl5_12 <=> sK3 = k2_mcart_1(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl5_16 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK3 = k2_mcart_1(sK4) | ~r2_hidden(k1_mcart_1(sK4),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK4,X1) | ~v1_relat_1(X1) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl5_16),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~r2_hidden(k1_mcart_1(sK4),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK4,X1) | ~v1_relat_1(X1) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl5_16),
% 0.20/0.52    inference(resolution,[],[f147,f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl5_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f141])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK1) | sK4 != X0 | k2_mcart_1(X0) = sK3 | ~r2_hidden(k1_mcart_1(X0),X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~m1_subset_1(k2_mcart_1(X0),sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK0)) )),
% 0.20/0.52    inference(resolution,[],[f146,f36])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | ~m1_subset_1(k2_mcart_1(X0),sK2) | sK4 != X0 | k2_mcart_1(X0) = sK3 | ~r2_hidden(k1_mcart_1(X0),X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(k1_mcart_1(X0)),sK1)) )),
% 0.20/0.52    inference(resolution,[],[f145,f36])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK1) | sK4 != X0 | ~m1_subset_1(k2_mcart_1(X0),sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK0) | k2_mcart_1(X0) = sK3 | ~r2_hidden(k1_mcart_1(X0),X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(superposition,[],[f111,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k2_mcart_1(X0),sK1) | ~m1_subset_1(X1,sK2) | ~m1_subset_1(k1_mcart_1(X0),sK0) | sK3 = X1 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(superposition,[],[f48,f35])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X7) )),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl5_16 | ~spl5_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f134,f129,f141])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~spl5_14),
% 0.20/0.52    inference(resolution,[],[f131,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    spl5_15 | ~spl5_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f133,f129,f136])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~spl5_14),
% 0.20/0.52    inference(resolution,[],[f131,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl5_14 | ~spl5_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f116,f81,f129])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_6),
% 0.20/0.52    inference(resolution,[],[f83,f41])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    spl5_13 | ~spl5_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f117,f81,f124])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK4),sK2) | ~spl5_6),
% 0.20/0.52    inference(resolution,[],[f83,f42])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl5_1 | ~spl5_5 | spl5_3 | spl5_2 | ~spl5_12 | spl5_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f78,f69,f119,f59,f64,f74,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl5_1 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl5_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl5_3 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl5_2 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl5_4 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | spl5_4),
% 0.20/0.52    inference(superposition,[],[f71,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) | spl5_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl5_2 | ~spl5_11),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    $false | (spl5_2 | ~spl5_11)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f61,f107,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | ~spl5_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl5_11 <=> v1_xboole_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    spl5_1 | ~spl5_10),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    $false | (spl5_1 | ~spl5_10)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f56,f103,f33])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    v1_xboole_0(sK0) | ~spl5_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    spl5_10 <=> v1_xboole_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f54])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    spl5_3 | ~spl5_9),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    $false | (spl5_3 | ~spl5_9)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f66,f97,f33])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    v1_xboole_0(sK2) | ~spl5_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl5_9 <=> v1_xboole_0(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl5_10 | spl5_11 | ~spl5_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f99,f91,f105,f101])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl5_8 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | v1_xboole_0(sK0) | ~spl5_8),
% 0.20/0.52    inference(resolution,[],[f93,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl5_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f91])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    spl5_8 | spl5_9 | ~spl5_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f89,f85,f95,f91])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl5_7 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    v1_xboole_0(sK2) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl5_7),
% 0.20/0.52    inference(resolution,[],[f87,f38])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f85])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl5_6 | spl5_7 | ~spl5_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f79,f74,f85,f81])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_5),
% 0.20/0.52    inference(resolution,[],[f76,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl5_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f47,f74])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.52    inference(definition_unfolding,[],[f28,f40])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ~spl5_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f32,f69])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f31,f64])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    k1_xboole_0 != sK2),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ~spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f59])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    k1_xboole_0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ~spl5_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f54])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (17069)------------------------------
% 0.20/0.52  % (17069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17069)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (17069)Memory used [KB]: 10874
% 0.20/0.52  % (17069)Time elapsed: 0.063 s
% 0.20/0.52  % (17069)------------------------------
% 0.20/0.52  % (17069)------------------------------
% 0.20/0.52  % (17047)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (17046)Success in time 0.163 s
%------------------------------------------------------------------------------
