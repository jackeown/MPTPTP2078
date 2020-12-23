%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 270 expanded)
%              Number of leaves         :   38 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  388 ( 767 expanded)
%              Number of equality atoms :   51 ( 130 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f347,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f105,f121,f136,f142,f156,f164,f169,f172,f194,f199,f204,f268,f281,f282,f307,f326,f336,f346])).

fof(f346,plain,(
    ~ spl8_31 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f45,f325,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f325,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl8_31
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f336,plain,(
    ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f45,f306,f60])).

fof(f306,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl8_29
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f326,plain,
    ( spl8_31
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f315,f191,f129,f323])).

fof(f129,plain,
    ( spl8_9
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f191,plain,
    ( spl8_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f315,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f314,f43])).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f314,plain,
    ( r2_hidden(sK0,k1_relat_1(k1_xboole_0))
    | ~ spl8_9
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f131,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f131,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f307,plain,
    ( ~ spl8_17
    | ~ spl8_16
    | spl8_10
    | spl8_29
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f289,f265,f304,f133,f196,f201])).

fof(f201,plain,
    ( spl8_17
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f196,plain,
    ( spl8_16
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f133,plain,
    ( spl8_10
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f265,plain,
    ( spl8_26
  <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f289,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f287,f43])).

fof(f287,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_26 ),
    inference(superposition,[],[f267,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 != X2
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f267,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f265])).

fof(f282,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f281,plain,
    ( ~ spl8_27
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f274,f261,f278])).

fof(f278,plain,
    ( spl8_27
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f261,plain,
    ( spl8_25
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f274,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_25 ),
    inference(superposition,[],[f71,f263])).

fof(f263,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f261])).

fof(f71,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f268,plain,
    ( spl8_25
    | spl8_26
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f250,f191,f154,f265,f261])).

fof(f154,plain,
    ( spl8_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f250,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(resolution,[],[f245,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1) )
    | ~ spl8_12
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f155,f193])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f204,plain,
    ( spl8_17
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f183,f158,f125,f201])).

fof(f125,plain,
    ( spl8_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f158,plain,
    ( spl8_13
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f183,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f126,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_13 ),
    inference(resolution,[],[f159,f54])).

fof(f159,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f126,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f199,plain,
    ( spl8_16
    | ~ spl8_1
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f177,f158,f84,f196])).

fof(f84,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f177,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f86,f176])).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f194,plain,
    ( spl8_15
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f176,f158,f191])).

fof(f172,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f86,f91,f96,f104,f120,f163,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f163,plain,
    ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_14
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f104,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f96,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f169,plain,
    ( spl8_11
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl8_11
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f55,f141,f159,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f141,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f164,plain,
    ( spl8_13
    | spl8_14
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f152,f118,f161,f158])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_7 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_7 ),
    inference(superposition,[],[f145,f143])).

fof(f143,plain,
    ( ! [X0] :
        ( k1_mcart_1(X0) = sK0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_7 ),
    inference(resolution,[],[f123,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f123,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl8_7 ),
    inference(resolution,[],[f120,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f145,plain,
    ( ! [X2] :
        ( r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl8_7 ),
    inference(resolution,[],[f123,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f156,plain,
    ( spl8_2
    | spl8_12
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f122,f118,f102,f84,f154,f89])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | k1_xboole_0 = sK1
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f120,f66])).

fof(f142,plain,
    ( ~ spl8_11
    | spl8_8 ),
    inference(avatar_split_clause,[],[f137,f125,f139])).

fof(f137,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_8 ),
    inference(resolution,[],[f127,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f136,plain,
    ( ~ spl8_8
    | spl8_9
    | ~ spl8_1
    | ~ spl8_10
    | spl8_3 ),
    inference(avatar_split_clause,[],[f99,f94,f133,f84,f129,f125])).

fof(f99,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl8_3 ),
    inference(superposition,[],[f96,f76])).

fof(f121,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f69,f118])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f105,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f70,f102])).

fof(f70,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f38,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f41,f94])).

fof(f41,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:43:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (27337)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (27338)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (27339)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (27329)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (27330)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (27334)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (27357)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (27341)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (27328)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (27351)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (27333)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (27331)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (27343)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (27342)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (27332)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (27352)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (27335)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (27336)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (27345)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (27349)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (27356)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (27354)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (27346)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (27355)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (27344)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (27350)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (27348)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (27340)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (27347)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (27350)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f347,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f87,f92,f97,f105,f121,f136,f142,f156,f164,f169,f172,f194,f199,f204,f268,f281,f282,f307,f326,f336,f346])).
% 0.22/0.56  fof(f346,plain,(
% 0.22/0.56    ~spl8_31),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f341])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    $false | ~spl8_31),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f45,f325,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.56  fof(f325,plain,(
% 0.22/0.56    r2_hidden(sK0,k1_xboole_0) | ~spl8_31),
% 0.22/0.56    inference(avatar_component_clause,[],[f323])).
% 0.22/0.56  fof(f323,plain,(
% 0.22/0.56    spl8_31 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f336,plain,(
% 0.22/0.56    ~spl8_29),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f331])).
% 0.22/0.56  fof(f331,plain,(
% 0.22/0.56    $false | ~spl8_29),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f45,f306,f60])).
% 0.22/0.56  fof(f306,plain,(
% 0.22/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | ~spl8_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f304])).
% 0.22/0.56  fof(f304,plain,(
% 0.22/0.56    spl8_29 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.22/0.56  fof(f326,plain,(
% 0.22/0.56    spl8_31 | ~spl8_9 | ~spl8_15),
% 0.22/0.56    inference(avatar_split_clause,[],[f315,f191,f129,f323])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    spl8_9 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.56  fof(f191,plain,(
% 0.22/0.56    spl8_15 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    r2_hidden(sK0,k1_xboole_0) | (~spl8_9 | ~spl8_15)),
% 0.22/0.56    inference(forward_demodulation,[],[f314,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.56  fof(f314,plain,(
% 0.22/0.56    r2_hidden(sK0,k1_relat_1(k1_xboole_0)) | (~spl8_9 | ~spl8_15)),
% 0.22/0.56    inference(forward_demodulation,[],[f131,f193])).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl8_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f191])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl8_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f129])).
% 0.22/0.56  fof(f307,plain,(
% 0.22/0.56    ~spl8_17 | ~spl8_16 | spl8_10 | spl8_29 | ~spl8_26),
% 0.22/0.56    inference(avatar_split_clause,[],[f289,f265,f304,f133,f196,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    spl8_17 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.56  fof(f196,plain,(
% 0.22/0.56    spl8_16 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    spl8_10 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.56  fof(f265,plain,(
% 0.22/0.56    spl8_26 <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.22/0.56  fof(f289,plain,(
% 0.22/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl8_26),
% 0.22/0.56    inference(forward_demodulation,[],[f287,f43])).
% 0.22/0.56  fof(f287,plain,(
% 0.22/0.56    r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl8_26),
% 0.22/0.56    inference(superposition,[],[f267,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 != X2 | k1_funct_1(X0,X1) = X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.57  fof(f267,plain,(
% 0.22/0.57    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | ~spl8_26),
% 0.22/0.57    inference(avatar_component_clause,[],[f265])).
% 0.22/0.57  fof(f282,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(sK2)),
% 0.22/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.57  fof(f281,plain,(
% 0.22/0.57    ~spl8_27 | ~spl8_25),
% 0.22/0.57    inference(avatar_split_clause,[],[f274,f261,f278])).
% 0.22/0.57  fof(f278,plain,(
% 0.22/0.57    spl8_27 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.22/0.57  fof(f261,plain,(
% 0.22/0.57    spl8_25 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.57  fof(f274,plain,(
% 0.22/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl8_25),
% 0.22/0.57    inference(superposition,[],[f71,f263])).
% 0.22/0.57  fof(f263,plain,(
% 0.22/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl8_25),
% 0.22/0.57    inference(avatar_component_clause,[],[f261])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f56,f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f57,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.22/0.57  fof(f268,plain,(
% 0.22/0.57    spl8_25 | spl8_26 | ~spl8_12 | ~spl8_15),
% 0.22/0.57    inference(avatar_split_clause,[],[f250,f191,f154,f265,f261])).
% 0.22/0.57  fof(f154,plain,(
% 0.22/0.57    spl8_12 <=> ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.57  fof(f250,plain,(
% 0.22/0.57    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl8_12 | ~spl8_15)),
% 0.22/0.57    inference(resolution,[],[f245,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(flattening,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.57  fof(f245,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1)) ) | (~spl8_12 | ~spl8_15)),
% 0.22/0.57    inference(forward_demodulation,[],[f155,f193])).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl8_12),
% 0.22/0.57    inference(avatar_component_clause,[],[f154])).
% 0.22/0.57  fof(f204,plain,(
% 0.22/0.57    spl8_17 | ~spl8_8 | ~spl8_13),
% 0.22/0.57    inference(avatar_split_clause,[],[f183,f158,f125,f201])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    spl8_8 <=> v1_relat_1(sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.57  fof(f158,plain,(
% 0.22/0.57    spl8_13 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.57  fof(f183,plain,(
% 0.22/0.57    v1_relat_1(k1_xboole_0) | (~spl8_8 | ~spl8_13)),
% 0.22/0.57    inference(backward_demodulation,[],[f126,f176])).
% 0.22/0.57  fof(f176,plain,(
% 0.22/0.57    k1_xboole_0 = sK2 | ~spl8_13),
% 0.22/0.57    inference(resolution,[],[f159,f54])).
% 0.22/0.57  fof(f159,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl8_13),
% 0.22/0.57    inference(avatar_component_clause,[],[f158])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    v1_relat_1(sK2) | ~spl8_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f125])).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    spl8_16 | ~spl8_1 | ~spl8_13),
% 0.22/0.57    inference(avatar_split_clause,[],[f177,f158,f84,f196])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    spl8_1 <=> v1_funct_1(sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.57  fof(f177,plain,(
% 0.22/0.57    v1_funct_1(k1_xboole_0) | (~spl8_1 | ~spl8_13)),
% 0.22/0.57    inference(backward_demodulation,[],[f86,f176])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    v1_funct_1(sK2) | ~spl8_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f84])).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    spl8_15 | ~spl8_13),
% 0.22/0.57    inference(avatar_split_clause,[],[f176,f158,f191])).
% 0.22/0.57  fof(f172,plain,(
% 0.22/0.57    ~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_7 | ~spl8_14),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    $false | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_7 | ~spl8_14)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f86,f91,f96,f104,f120,f163,f66])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.57    inference(flattening,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_14),
% 0.22/0.57    inference(avatar_component_clause,[],[f161])).
% 0.22/0.57  fof(f161,plain,(
% 0.22/0.57    spl8_14 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl8_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f118])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.57  fof(f104,plain,(
% 0.22/0.57    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl8_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f102])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    spl8_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl8_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f94])).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    spl8_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | spl8_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    spl8_2 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.57  fof(f169,plain,(
% 0.22/0.57    spl8_11 | ~spl8_13),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    $false | (spl8_11 | ~spl8_13)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f55,f141,f159,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    ~v1_xboole_0(sK2) | spl8_11),
% 0.22/0.57    inference(avatar_component_clause,[],[f139])).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    spl8_11 <=> v1_xboole_0(sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.57  fof(f164,plain,(
% 0.22/0.57    spl8_13 | spl8_14 | ~spl8_7),
% 0.22/0.57    inference(avatar_split_clause,[],[f152,f118,f161,f158])).
% 0.22/0.57  fof(f152,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl8_7),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f151])).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl8_7),
% 0.22/0.57    inference(superposition,[],[f145,f143])).
% 0.22/0.57  fof(f143,plain,(
% 0.22/0.57    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) ) | ~spl8_7),
% 0.22/0.57    inference(resolution,[],[f123,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.22/0.57    inference(definition_unfolding,[],[f64,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f46,f67])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl8_7),
% 0.22/0.57    inference(resolution,[],[f120,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.57  fof(f145,plain,(
% 0.22/0.57    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) ) | ~spl8_7),
% 0.22/0.57    inference(resolution,[],[f123,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    spl8_2 | spl8_12 | ~spl8_1 | ~spl8_4 | ~spl8_7),
% 0.22/0.57    inference(avatar_split_clause,[],[f122,f118,f102,f84,f154,f89])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl8_7),
% 0.22/0.57    inference(resolution,[],[f120,f66])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ~spl8_11 | spl8_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f137,f125,f139])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    ~v1_xboole_0(sK2) | spl8_8),
% 0.22/0.57    inference(resolution,[],[f127,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | spl8_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f125])).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    ~spl8_8 | spl8_9 | ~spl8_1 | ~spl8_10 | spl8_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f99,f94,f133,f84,f129,f125])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    ~r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl8_3),
% 0.22/0.57    inference(superposition,[],[f96,f76])).
% 0.22/0.57  fof(f121,plain,(
% 0.22/0.57    spl8_7),
% 0.22/0.57    inference(avatar_split_clause,[],[f69,f118])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.57    inference(definition_unfolding,[],[f39,f68])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.57    inference(negated_conjecture,[],[f19])).
% 0.22/0.57  fof(f19,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    spl8_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f70,f102])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.57    inference(definition_unfolding,[],[f38,f68])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ~spl8_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f41,f94])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    ~spl8_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f40,f89])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    k1_xboole_0 != sK1),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    spl8_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f37,f84])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    v1_funct_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (27350)------------------------------
% 0.22/0.57  % (27350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (27350)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (27350)Memory used [KB]: 10874
% 0.22/0.57  % (27350)Time elapsed: 0.152 s
% 0.22/0.57  % (27350)------------------------------
% 0.22/0.57  % (27350)------------------------------
% 0.22/0.57  % (27327)Success in time 0.201 s
%------------------------------------------------------------------------------
