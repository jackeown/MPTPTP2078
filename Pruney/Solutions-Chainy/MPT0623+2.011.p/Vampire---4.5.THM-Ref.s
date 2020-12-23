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
% DateTime   : Thu Dec  3 12:52:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 154 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 ( 591 expanded)
%              Number of equality atoms :  112 ( 271 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f79,f96,f97,f99,f130,f135,f138])).

fof(f138,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f136,f62])).

fof(f62,plain,
    ( k1_xboole_0 != sK0
    | spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f136,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_6 ),
    inference(resolution,[],[f126,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f126,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f135,plain,
    ( spl5_2
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f133,f65])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(superposition,[],[f129,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f129,plain,
    ( ! [X0] :
        ( sK1 != k1_relat_1(sK2(X0,sK3(sK0)))
        | k1_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | sK1 != k1_relat_1(sK2(X0,sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f130,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f122,f128,f124])).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | sK1 != k1_relat_1(sK2(X0,sK3(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

% (12405)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | sK1 != k1_relat_1(sK2(X0,X1)) ) ),
    inference(resolution,[],[f119,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f119,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_tarski(X3,X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f118,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_tarski(X3,X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_tarski(X3,X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_funct_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f34,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK2(X0,X1)) = k2_tarski(X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f99,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl5_5 ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,
    ( ! [X4] : k1_xboole_0 != X4
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_5
  <=> ! [X4] : k1_xboole_0 != X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f97,plain,
    ( spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f92,f72,f94])).

fof(f72,plain,
    ( spl5_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,(
    ! [X5] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X5 ) ),
    inference(superposition,[],[f50,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f83,f52])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK4(X0))
      | k1_xboole_0 = sK4(X0) ) ),
    inference(resolution,[],[f42,f50])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f50,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,
    ( spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f91,f76,f94])).

fof(f76,plain,
    ( spl5_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f91,plain,(
    ! [X4] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X4 ) ),
    inference(superposition,[],[f51,f87])).

fof(f51,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f70,f64,f76,f72])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f69,f36])).

fof(f36,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f69,plain,
    ( k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f33,f64,f60])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:14:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (12429)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (12420)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (12428)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (12420)Refutation not found, incomplete strategy% (12420)------------------------------
% 0.20/0.51  % (12420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12420)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12420)Memory used [KB]: 6140
% 0.20/0.51  % (12420)Time elapsed: 0.003 s
% 0.20/0.51  % (12420)------------------------------
% 0.20/0.51  % (12420)------------------------------
% 0.20/0.51  % (12408)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (12410)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (12408)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (12412)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (12415)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (12414)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (12411)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12419)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f67,f79,f96,f97,f99,f130,f135,f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    spl5_1 | ~spl5_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    $false | (spl5_1 | ~spl5_6)),
% 0.20/0.52    inference(subsumption_resolution,[],[f136,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl5_1 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl5_6),
% 0.20/0.52    inference(resolution,[],[f126,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    v1_xboole_0(sK0) | ~spl5_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f124])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl5_6 <=> v1_xboole_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl5_2 | ~spl5_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    $false | (spl5_2 | ~spl5_7)),
% 0.20/0.52    inference(subsumption_resolution,[],[f133,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl5_2 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl5_7),
% 0.20/0.52    inference(equality_resolution,[],[f132])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl5_7),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl5_7),
% 0.20/0.52    inference(superposition,[],[f129,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 != k1_relat_1(sK2(X0,sK3(sK0))) | k1_xboole_0 = X0) ) | ~spl5_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    spl5_7 <=> ! [X0] : (k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,sK3(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    spl5_6 | spl5_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f122,f128,f124])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,sK3(sK0))) | v1_xboole_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f120,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  % (12405)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(rectify,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f119,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f55,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X3,X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f118,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X3,X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f114,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X3,X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_funct_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.20/0.52    inference(superposition,[],[f34,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_relat_1(sK2(X0,X1)) = k2_tarski(X1,X1) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f47,f39])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ~spl5_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    $false | ~spl5_5),
% 0.20/0.52    inference(equality_resolution,[],[f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X4] : (k1_xboole_0 != X4) ) | ~spl5_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl5_5 <=> ! [X4] : k1_xboole_0 != X4),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    spl5_5 | spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f92,f72,f94])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    spl5_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X5] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X5) )),
% 0.20/0.52    inference(superposition,[],[f50,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = sK4(X0) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(superposition,[],[f83,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK4(X0)) | k1_xboole_0 = sK4(X0)) )),
% 0.20/0.52    inference(resolution,[],[f42,f50])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl5_5 | spl5_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f91,f76,f94])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl5_4 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X4] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X4) )),
% 0.20/0.52    inference(superposition,[],[f51,f87])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ~spl5_3 | ~spl5_4 | ~spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f70,f64,f76,f72])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f69,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    k1_relat_1(k1_xboole_0) != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f68,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(superposition,[],[f34,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~spl5_1 | spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f33,f64,f60])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (12408)------------------------------
% 0.20/0.52  % (12408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12408)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (12408)Memory used [KB]: 10746
% 0.20/0.52  % (12408)Time elapsed: 0.104 s
% 0.20/0.52  % (12408)------------------------------
% 0.20/0.52  % (12408)------------------------------
% 0.20/0.53  % (12401)Success in time 0.163 s
%------------------------------------------------------------------------------
