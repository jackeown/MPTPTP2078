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
% DateTime   : Thu Dec  3 12:55:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 166 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  338 ( 533 expanded)
%              Number of equality atoms :   50 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f62,f67,f76,f80,f84,f88,f96,f116,f121,f126,f135,f140,f145,f155,f169,f181])).

fof(f181,plain,
    ( ~ spl3_4
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f175,f61])).

fof(f61,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f175,plain,
    ( ! [X1] : ~ r1_xboole_0(k1_enumset1(sK1(sK0,k1_xboole_0),sK1(sK0,k1_xboole_0),X1),k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f168,f95])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f168,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_23
  <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f169,plain,
    ( spl3_23
    | spl3_3
    | ~ spl3_5
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f164,f153,f137,f132,f64,f55,f166])).

fof(f55,plain,
    ( spl3_3
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f132,plain,
    ( spl3_19
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f137,plain,
    ( spl3_20
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f153,plain,
    ( spl3_22
  <=> ! [X0] :
        ( r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | v5_funct_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f164,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | spl3_3
    | ~ spl3_5
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f163,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f163,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f162,f57])).

fof(f57,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f162,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | v5_funct_1(k1_xboole_0,sK0)
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f158,f139])).

fof(f139,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f158,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | v5_funct_1(k1_xboole_0,sK0)
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(resolution,[],[f154,f134])).

fof(f134,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v5_funct_1(X0,sK0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f149,f143,f50,f45,f153])).

fof(f45,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f143,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( v5_funct_1(X1,X0)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f149,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | v5_funct_1(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f146,f47])).

fof(f47,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f146,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(sK0,X0),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | v5_funct_1(X0,sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f144,f52])).

fof(f52,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v5_funct_1(X1,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f35,f143])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f140,plain,
    ( spl3_20
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f130,f124,f74,f137])).

fof(f74,plain,
    ( spl3_7
  <=> ! [X1,X0] : v1_relat_1(sK2(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f124,plain,
    ( spl3_18
  <=> ! [X0] : k1_xboole_0 = sK2(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f130,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(superposition,[],[f75,f125])).

fof(f125,plain,
    ( ! [X0] : k1_xboole_0 = sK2(k1_xboole_0,X0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f75,plain,
    ( ! [X0,X1] : v1_relat_1(sK2(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f135,plain,
    ( spl3_19
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f129,f124,f78,f132])).

fof(f78,plain,
    ( spl3_8
  <=> ! [X1,X0] : v1_funct_1(sK2(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f129,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(superposition,[],[f79,f125])).

fof(f79,plain,
    ( ! [X0,X1] : v1_funct_1(sK2(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f126,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f122,f119,f124])).

fof(f119,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( k1_xboole_0 != X0
        | k1_xboole_0 = sK2(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f122,plain,
    ( ! [X0] : k1_xboole_0 = sK2(k1_xboole_0,X0)
    | ~ spl3_17 ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != X0
        | k1_xboole_0 = sK2(X0,X1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl3_17
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f117,f114,f82,f119])).

fof(f82,plain,
    ( spl3_9
  <=> ! [X1,X0] : k1_relat_1(sK2(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f114,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = sK2(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != X0
        | k1_xboole_0 = sK2(X0,X1) )
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(superposition,[],[f115,f83])).

fof(f83,plain,
    ( ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = sK2(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl3_16
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f98,f86,f74,f114])).

fof(f86,plain,
    ( spl3_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = sK2(X0,X1) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f87,f75])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f88,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f84,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f80,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f58,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.43  % (10642)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.44  % (10642)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f182,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f48,f53,f58,f62,f67,f76,f80,f84,f88,f96,f116,f121,f126,f135,f140,f145,f155,f169,f181])).
% 0.22/0.44  fof(f181,plain,(
% 0.22/0.44    ~spl3_4 | ~spl3_12 | ~spl3_23),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f180])).
% 0.22/0.44  fof(f180,plain,(
% 0.22/0.44    $false | (~spl3_4 | ~spl3_12 | ~spl3_23)),
% 0.22/0.44    inference(subsumption_resolution,[],[f175,f61])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl3_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f175,plain,(
% 0.22/0.44    ( ! [X1] : (~r1_xboole_0(k1_enumset1(sK1(sK0,k1_xboole_0),sK1(sK0,k1_xboole_0),X1),k1_xboole_0)) ) | (~spl3_12 | ~spl3_23)),
% 0.22/0.44    inference(resolution,[],[f168,f95])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) ) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f94])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    spl3_12 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f168,plain,(
% 0.22/0.44    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_23),
% 0.22/0.44    inference(avatar_component_clause,[],[f166])).
% 0.22/0.44  fof(f166,plain,(
% 0.22/0.44    spl3_23 <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.44  fof(f169,plain,(
% 0.22/0.44    spl3_23 | spl3_3 | ~spl3_5 | ~spl3_19 | ~spl3_20 | ~spl3_22),
% 0.22/0.44    inference(avatar_split_clause,[],[f164,f153,f137,f132,f64,f55,f166])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl3_3 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl3_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f132,plain,(
% 0.22/0.44    spl3_19 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    spl3_20 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.44  fof(f153,plain,(
% 0.22/0.44    spl3_22 <=> ! [X0] : (r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(X0,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.44  fof(f164,plain,(
% 0.22/0.44    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | (spl3_3 | ~spl3_5 | ~spl3_19 | ~spl3_20 | ~spl3_22)),
% 0.22/0.44    inference(forward_demodulation,[],[f163,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f64])).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | (spl3_3 | ~spl3_19 | ~spl3_20 | ~spl3_22)),
% 0.22/0.44    inference(subsumption_resolution,[],[f162,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0) | spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f55])).
% 0.22/0.44  fof(f162,plain,(
% 0.22/0.44    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | v5_funct_1(k1_xboole_0,sK0) | (~spl3_19 | ~spl3_20 | ~spl3_22)),
% 0.22/0.44    inference(subsumption_resolution,[],[f158,f139])).
% 0.22/0.44  fof(f139,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | ~spl3_20),
% 0.22/0.44    inference(avatar_component_clause,[],[f137])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | v5_funct_1(k1_xboole_0,sK0) | (~spl3_19 | ~spl3_22)),
% 0.22/0.44    inference(resolution,[],[f154,f134])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    v1_funct_1(k1_xboole_0) | ~spl3_19),
% 0.22/0.44    inference(avatar_component_clause,[],[f132])).
% 0.22/0.44  fof(f154,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | ~v1_relat_1(X0) | v5_funct_1(X0,sK0)) ) | ~spl3_22),
% 0.22/0.44    inference(avatar_component_clause,[],[f153])).
% 0.22/0.44  fof(f155,plain,(
% 0.22/0.44    spl3_22 | ~spl3_1 | ~spl3_2 | ~spl3_21),
% 0.22/0.44    inference(avatar_split_clause,[],[f149,f143,f50,f45,f153])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl3_1 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_2 <=> v1_funct_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f143,plain,(
% 0.22/0.44    spl3_21 <=> ! [X1,X0] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.44  fof(f149,plain,(
% 0.22/0.44    ( ! [X0] : (r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(X0,sK0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_21)),
% 0.22/0.44    inference(subsumption_resolution,[],[f146,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f45])).
% 0.22/0.44  fof(f146,plain,(
% 0.22/0.44    ( ! [X0] : (r2_hidden(sK1(sK0,X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(X0,sK0) | ~v1_relat_1(sK0)) ) | (~spl3_2 | ~spl3_21)),
% 0.22/0.44    inference(resolution,[],[f144,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    v1_funct_1(sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v5_funct_1(X1,X0) | ~v1_relat_1(X0)) ) | ~spl3_21),
% 0.22/0.44    inference(avatar_component_clause,[],[f143])).
% 0.22/0.44  fof(f145,plain,(
% 0.22/0.44    spl3_21),
% 0.22/0.44    inference(avatar_split_clause,[],[f35,f143])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(rectify,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.44  fof(f140,plain,(
% 0.22/0.44    spl3_20 | ~spl3_7 | ~spl3_18),
% 0.22/0.44    inference(avatar_split_clause,[],[f130,f124,f74,f137])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : v1_relat_1(sK2(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    spl3_18 <=> ! [X0] : k1_xboole_0 = sK2(k1_xboole_0,X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | (~spl3_7 | ~spl3_18)),
% 0.22/0.44    inference(superposition,[],[f75,f125])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = sK2(k1_xboole_0,X0)) ) | ~spl3_18),
% 0.22/0.44    inference(avatar_component_clause,[],[f124])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f74])).
% 0.22/0.44  fof(f135,plain,(
% 0.22/0.44    spl3_19 | ~spl3_8 | ~spl3_18),
% 0.22/0.44    inference(avatar_split_clause,[],[f129,f124,f78,f132])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl3_8 <=> ! [X1,X0] : v1_funct_1(sK2(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f129,plain,(
% 0.22/0.44    v1_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_18)),
% 0.22/0.44    inference(superposition,[],[f79,f125])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f78])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    spl3_18 | ~spl3_17),
% 0.22/0.44    inference(avatar_split_clause,[],[f122,f119,f124])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    spl3_17 <=> ! [X1,X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK2(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = sK2(k1_xboole_0,X0)) ) | ~spl3_17),
% 0.22/0.44    inference(equality_resolution,[],[f120])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK2(X0,X1)) ) | ~spl3_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f119])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    spl3_17 | ~spl3_9 | ~spl3_16),
% 0.22/0.44    inference(avatar_split_clause,[],[f117,f114,f82,f119])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X0] : k1_relat_1(sK2(X0,X1)) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    spl3_16 <=> ! [X1,X0] : (k1_xboole_0 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = sK2(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK2(X0,X1)) ) | (~spl3_9 | ~spl3_16)),
% 0.22/0.44    inference(superposition,[],[f115,f83])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f82])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = sK2(X0,X1)) ) | ~spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f114])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    spl3_16 | ~spl3_7 | ~spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f98,f86,f74,f114])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    spl3_10 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = sK2(X0,X1)) ) | (~spl3_7 | ~spl3_10)),
% 0.22/0.44    inference(resolution,[],[f87,f75])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f86])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f43,f94])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f42,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f86])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f40,f82])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f39,f78])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f38,f74])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f31,f60])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f55])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f8])).
% 0.22/0.44  fof(f8,conjecture,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f50])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    v1_funct_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f45])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (10642)------------------------------
% 0.22/0.44  % (10642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (10642)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (10642)Memory used [KB]: 6140
% 0.22/0.44  % (10642)Time elapsed: 0.008 s
% 0.22/0.44  % (10642)------------------------------
% 0.22/0.44  % (10642)------------------------------
% 0.22/0.44  % (10634)Success in time 0.079 s
%------------------------------------------------------------------------------
