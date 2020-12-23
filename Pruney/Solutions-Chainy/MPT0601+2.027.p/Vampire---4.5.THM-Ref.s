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
% DateTime   : Thu Dec  3 12:51:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 238 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 482 expanded)
%              Number of equality atoms :   74 ( 198 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f79,f87,f119,f128,f137,f195,f227,f235,f250,f256])).

fof(f256,plain,(
    ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f35,f148])).

fof(f148,plain,
    ( ! [X1] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X1)
    | ~ spl2_9 ),
    inference(superposition,[],[f60,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_9
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f250,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f246,f91,f76,f105])).

fof(f105,plain,
    ( spl2_6
  <=> k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f76,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f91,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f246,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f78,f93,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f93,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f78,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f235,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f233,f84,f91])).

fof(f84,plain,
    ( spl2_4
  <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f233,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f86,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f227,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f204,f117,f70,f91])).

fof(f70,plain,
    ( spl2_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f117,plain,
    ( spl2_8
  <=> ! [X1] :
        ( k1_xboole_0 != k11_relat_1(sK1,X1)
        | r1_xboole_0(k1_relat_1(sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f204,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f72,f118])).

fof(f118,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k11_relat_1(sK1,X1)
        | r1_xboole_0(k1_relat_1(sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f72,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f195,plain,
    ( spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f193,f66,f134])).

fof(f134,plain,
    ( spl2_10
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f66,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f193,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f140,f67])).

fof(f67,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),k1_relat_1(sK1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f67,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f137,plain,
    ( ~ spl2_3
    | spl2_9
    | ~ spl2_10
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f126,f105,f134,f130,f76])).

fof(f126,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(superposition,[],[f42,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f128,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f122,f105,f76,f70])).

fof(f122,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f98,f107])).

fof(f98,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f119,plain,
    ( ~ spl2_3
    | spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f111,f76,f117,f76])).

fof(f111,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k11_relat_1(sK1,X1)
        | r1_xboole_0(k1_relat_1(sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3 ),
    inference(superposition,[],[f40,f98])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,
    ( spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f81,f66,f84])).

fof(f81,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f68,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f68,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f74,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f33,f70,f66])).

fof(f33,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f34,f70,f66])).

fof(f34,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (8874)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (8880)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (8879)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (8880)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f257,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f73,f74,f79,f87,f119,f128,f137,f195,f227,f235,f250,f256])).
% 0.20/0.46  fof(f256,plain,(
% 0.20/0.46    ~spl2_9),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f252])).
% 0.20/0.46  fof(f252,plain,(
% 0.20/0.46    $false | ~spl2_9),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f35,f148])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,X1)) ) | ~spl2_9),
% 0.20/0.46    inference(superposition,[],[f60,f132])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl2_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f130])).
% 0.20/0.46  fof(f130,plain,(
% 0.20/0.46    spl2_9 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f38,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f36,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f39,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f45,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f49,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f50,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f51,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.46  fof(f250,plain,(
% 0.20/0.46    spl2_6 | ~spl2_3 | ~spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f246,f91,f76,f105])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    spl2_6 <=> k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl2_5 <=> r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f246,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl2_3 | ~spl2_5)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f78,f93,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f91])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f76])).
% 0.20/0.46  fof(f235,plain,(
% 0.20/0.46    spl2_5 | ~spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f233,f84,f91])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl2_4 <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f233,plain,(
% 0.20/0.46    r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 0.20/0.46    inference(resolution,[],[f86,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f84])).
% 0.20/0.46  fof(f227,plain,(
% 0.20/0.46    spl2_5 | ~spl2_2 | ~spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f204,f117,f70,f91])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl2_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    spl2_8 <=> ! [X1] : (k1_xboole_0 != k11_relat_1(sK1,X1) | r1_xboole_0(k1_relat_1(sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f204,plain,(
% 0.20/0.46    r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl2_2 | ~spl2_8)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f72,f118])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 != k11_relat_1(sK1,X1) | r1_xboole_0(k1_relat_1(sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f117])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f70])).
% 0.20/0.46  fof(f195,plain,(
% 0.20/0.46    spl2_10 | ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f193,f66,f134])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    spl2_10 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    spl2_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | ~spl2_1),
% 0.20/0.46    inference(resolution,[],[f140,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f66])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),k1_relat_1(sK1))) ) | ~spl2_1),
% 0.20/0.46    inference(resolution,[],[f67,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f48,f57])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.46    inference(flattening,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.46    inference(nnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    ~spl2_3 | spl2_9 | ~spl2_10 | ~spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f126,f105,f134,f130,f76])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~v1_relat_1(sK1) | ~spl2_6),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f123])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~v1_relat_1(sK1) | ~spl2_6),
% 0.20/0.46    inference(superposition,[],[f42,f107])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f105])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    spl2_2 | ~spl2_3 | ~spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f122,f105,f76,f70])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    k1_xboole_0 = k11_relat_1(sK1,sK0) | (~spl2_3 | ~spl2_6)),
% 0.20/0.47    inference(superposition,[],[f98,f107])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | ~spl2_3),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f78,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f37,f58])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~spl2_3 | spl2_8 | ~spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f111,f76,f117,f76])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 != k11_relat_1(sK1,X1) | r1_xboole_0(k1_relat_1(sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(sK1)) ) | ~spl2_3),
% 0.20/0.47    inference(superposition,[],[f40,f98])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl2_4 | spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f81,f66,f84])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | spl2_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f68,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f43,f58])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f76])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f16])).
% 0.20/0.47  fof(f16,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl2_1 | ~spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f70,f66])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~spl2_1 | spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f70,f66])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (8880)------------------------------
% 0.20/0.47  % (8880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (8880)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (8880)Memory used [KB]: 6268
% 0.20/0.47  % (8880)Time elapsed: 0.057 s
% 0.20/0.47  % (8880)------------------------------
% 0.20/0.47  % (8880)------------------------------
% 0.20/0.47  % (8873)Success in time 0.113 s
%------------------------------------------------------------------------------
