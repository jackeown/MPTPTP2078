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
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 174 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  267 ( 705 expanded)
%              Number of equality atoms :   48 ( 154 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f79,f117,f172])).

fof(f172,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f166,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f166,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f139,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f139,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(X0,k2_tarski(sK1,sK1)))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f132,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f132,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f122,f130])).

fof(f130,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f118,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f118,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f32,f64,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

fof(f64,plain,
    ( v3_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> v3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

fof(f122,plain,
    ( r2_hidden(sK1,k4_xboole_0(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)))
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f69,f74,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f74,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f61,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f117,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f60,f99,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f99,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))
    | spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f84,f89])).

fof(f89,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f83,f78])).

fof(f78,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK0))
        | k1_xboole_0 = X2 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_4
  <=> ! [X2] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X2,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f83,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)),k2_relat_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f32,f65,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f39,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( ~ v3_relat_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f84,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)),k2_tarski(k1_xboole_0,k1_xboole_0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f33,f77,f63])).

fof(f33,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK0))
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f34,f72,f63])).

fof(f34,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f67,f63])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (7759)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (7778)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (7778)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f70,f75,f79,f117,f172])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f166,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(superposition,[],[f139,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,k4_xboole_0(X0,k2_tarski(sK1,sK1)))) ) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f61,f132,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_xboole_0) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(backward_demodulation,[],[f122,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl3_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f118,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl3_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f64,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f38,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (((v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) & (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    v3_relat_1(sK0) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl3_1 <=> v3_relat_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ((k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0)) => ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) => (k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    r2_hidden(sK1,k4_xboole_0(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))) | (spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f69,f74,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f53,f37])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    r2_hidden(sK1,k2_relat_1(sK0)) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_3 <=> r2_hidden(sK1,k2_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f52,f37])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl3_1 | ~spl3_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    $false | (spl3_1 | ~spl3_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f60,f99,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ~r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) | (spl3_1 | ~spl3_4)),
% 0.21/0.50    inference(backward_demodulation,[],[f84,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | (spl3_1 | ~spl3_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f83,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK0)) | k1_xboole_0 = X2) ) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl3_4 <=> ! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    r2_hidden(sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)),k2_relat_1(sK0)) | spl3_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f80,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | spl3_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f65,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f39,f37])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~v3_relat_1(sK0) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~r2_hidden(sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)),k2_tarski(k1_xboole_0,k1_xboole_0)) | spl3_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f80,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl3_1 | spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f77,f63])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0)) | v3_relat_1(sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~spl3_1 | spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f72,f63])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    r2_hidden(sK1,k2_relat_1(sK0)) | ~v3_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f67,f63])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | ~v3_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (7778)------------------------------
% 0.21/0.50  % (7778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7778)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (7778)Memory used [KB]: 10746
% 0.21/0.51  % (7778)Time elapsed: 0.087 s
% 0.21/0.51  % (7778)------------------------------
% 0.21/0.51  % (7778)------------------------------
% 0.21/0.52  % (7751)Success in time 0.159 s
%------------------------------------------------------------------------------
