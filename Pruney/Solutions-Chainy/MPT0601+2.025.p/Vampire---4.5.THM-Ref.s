%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 249 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 ( 513 expanded)
%              Number of equality atoms :   80 ( 213 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f81,f89,f96,f104,f113,f124,f132,f154,f168,f193])).

fof(f193,plain,
    ( ~ spl2_3
    | spl2_7
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl2_3
    | spl2_7
    | ~ spl2_9 ),
    inference(global_subsumption,[],[f78,f191])).

fof(f191,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f111,f131])).

fof(f131,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_9
  <=> ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f111,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_7
  <=> k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f78,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_3
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f168,plain,
    ( ~ spl2_3
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl2_3
    | spl2_8 ),
    inference(global_subsumption,[],[f35,f78,f125])).

fof(f125,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_8 ),
    inference(unit_resulting_resolution,[],[f123,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f123,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_8
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f35,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
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

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f154,plain,
    ( ~ spl2_7
    | spl2_8
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl2_7
    | spl2_8
    | ~ spl2_9 ),
    inference(global_subsumption,[],[f35,f125,f133])).

fof(f133,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f131,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f132,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f127,f68,f130])).

fof(f68,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f127,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f70,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f124,plain,
    ( ~ spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f114,f110,f68,f121])).

fof(f114,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f70,f82,f112,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[],[f63,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f63,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f113,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f105,f101,f68,f110])).

fof(f101,plain,
    ( spl2_6
  <=> r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f105,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f70,f103,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f103,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f104,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f97,f93,f68,f101])).

fof(f93,plain,
    ( spl2_5
  <=> k1_xboole_0 = k7_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f97,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f70,f95,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f95,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f90,f86,f68,f93])).

fof(f86,plain,
    ( spl2_4
  <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f90,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f70,f88,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f88,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f89,plain,
    ( spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f83,f73,f86])).

fof(f73,plain,
    ( spl2_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f83,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f74,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f74,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f81,plain,
    ( ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f36,f77,f73])).

fof(f36,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:57:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.41  % (22625)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.42  % (22625)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f194,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f71,f81,f89,f96,f104,f113,f124,f132,f154,f168,f193])).
% 0.19/0.42  fof(f193,plain,(
% 0.19/0.42    ~spl2_3 | spl2_7 | ~spl2_9),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f192])).
% 0.19/0.42  fof(f192,plain,(
% 0.19/0.42    $false | (~spl2_3 | spl2_7 | ~spl2_9)),
% 0.19/0.42    inference(global_subsumption,[],[f78,f191])).
% 0.19/0.42  fof(f191,plain,(
% 0.19/0.42    k1_xboole_0 != k11_relat_1(sK1,sK0) | (spl2_7 | ~spl2_9)),
% 0.19/0.42    inference(superposition,[],[f111,f131])).
% 0.19/0.42  fof(f131,plain,(
% 0.19/0.42    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | ~spl2_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f130])).
% 0.19/0.42  fof(f130,plain,(
% 0.19/0.42    spl2_9 <=> ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.42  fof(f111,plain,(
% 0.19/0.42    k1_xboole_0 != k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl2_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f110])).
% 0.19/0.42  fof(f110,plain,(
% 0.19/0.42    spl2_7 <=> k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f77])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    spl2_3 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.42  fof(f168,plain,(
% 0.19/0.42    ~spl2_3 | spl2_8),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f167])).
% 0.19/0.42  fof(f167,plain,(
% 0.19/0.42    $false | (~spl2_3 | spl2_8)),
% 0.19/0.42    inference(global_subsumption,[],[f35,f78,f125])).
% 0.19/0.42  fof(f125,plain,(
% 0.19/0.42    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_8),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f123,f65])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f50,f61])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f38,f60])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f42,f59])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f51,f58])).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f52,f57])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f53,f56])).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f54,f55])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.19/0.42    inference(nnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.19/0.42  fof(f123,plain,(
% 0.19/0.42    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | spl2_8),
% 0.19/0.42    inference(avatar_component_clause,[],[f121])).
% 0.19/0.42  fof(f121,plain,(
% 0.19/0.42    spl2_8 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.19/0.42    inference(nnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.42    inference(negated_conjecture,[],[f17])).
% 0.19/0.42  fof(f17,conjecture,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.19/0.42  fof(f154,plain,(
% 0.19/0.42    ~spl2_7 | spl2_8 | ~spl2_9),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f153])).
% 0.19/0.42  fof(f153,plain,(
% 0.19/0.42    $false | (~spl2_7 | spl2_8 | ~spl2_9)),
% 0.19/0.42    inference(global_subsumption,[],[f35,f125,f133])).
% 0.19/0.42  fof(f133,plain,(
% 0.19/0.42    k1_xboole_0 = k11_relat_1(sK1,sK0) | (~spl2_7 | ~spl2_9)),
% 0.19/0.42    inference(superposition,[],[f131,f112])).
% 0.19/0.42  fof(f112,plain,(
% 0.19/0.42    k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f110])).
% 0.19/0.42  fof(f132,plain,(
% 0.19/0.42    spl2_9 | ~spl2_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f127,f68,f130])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    spl2_1 <=> v1_relat_1(sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.42  fof(f127,plain,(
% 0.19/0.42    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | ~spl2_1),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f62])).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f39,f61])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    v1_relat_1(sK1) | ~spl2_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f68])).
% 0.19/0.42  fof(f124,plain,(
% 0.19/0.42    ~spl2_8 | ~spl2_1 | ~spl2_7),
% 0.19/0.42    inference(avatar_split_clause,[],[f114,f110,f68,f121])).
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_7)),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f82,f112,f47])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.19/0.42  fof(f82,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.42    inference(superposition,[],[f63,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f41,f61])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,axiom,(
% 0.19/0.42    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.19/0.42  fof(f113,plain,(
% 0.19/0.42    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.19/0.42    inference(avatar_split_clause,[],[f105,f101,f68,f110])).
% 0.19/0.42  fof(f101,plain,(
% 0.19/0.42    spl2_6 <=> r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.42  fof(f105,plain,(
% 0.19/0.42    k1_xboole_0 = k9_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_6)),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f103,f46])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f32])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(nnf_transformation,[],[f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.19/0.42  fof(f103,plain,(
% 0.19/0.42    r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f101])).
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    spl2_6 | ~spl2_1 | ~spl2_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f97,f93,f68,f101])).
% 0.19/0.42  fof(f93,plain,(
% 0.19/0.42    spl2_5 <=> k1_xboole_0 = k7_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.42  fof(f97,plain,(
% 0.19/0.42    r1_xboole_0(k1_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_5)),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f95,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f31])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(nnf_transformation,[],[f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.19/0.42  fof(f95,plain,(
% 0.19/0.42    k1_xboole_0 = k7_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl2_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f93])).
% 0.19/0.42  fof(f96,plain,(
% 0.19/0.42    spl2_5 | ~spl2_1 | ~spl2_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f90,f86,f68,f93])).
% 0.19/0.42  fof(f86,plain,(
% 0.19/0.42    spl2_4 <=> r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    k1_xboole_0 = k7_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl2_1 | ~spl2_4)),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f70,f88,f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | ~spl2_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f86])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    spl2_4 | spl2_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f83,f73,f86])).
% 0.19/0.42  fof(f73,plain,(
% 0.19/0.42    spl2_2 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.42  fof(f83,plain,(
% 0.19/0.42    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_relat_1(sK1)) | spl2_2),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f74,f64])).
% 0.19/0.42  fof(f64,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f48,f61])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,axiom,(
% 0.19/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.42  fof(f74,plain,(
% 0.19/0.42    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f73])).
% 0.19/0.42  fof(f81,plain,(
% 0.19/0.42    ~spl2_2 | spl2_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f36,f77,f73])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f30])).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    spl2_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f34,f68])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    v1_relat_1(sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f30])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (22625)------------------------------
% 0.19/0.42  % (22625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (22625)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (22625)Memory used [KB]: 10746
% 0.19/0.42  % (22625)Time elapsed: 0.009 s
% 0.19/0.42  % (22625)------------------------------
% 0.19/0.42  % (22625)------------------------------
% 0.19/0.42  % (22606)Success in time 0.074 s
%------------------------------------------------------------------------------
