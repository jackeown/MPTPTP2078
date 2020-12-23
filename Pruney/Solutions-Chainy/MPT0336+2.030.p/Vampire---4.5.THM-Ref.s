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
% DateTime   : Thu Dec  3 12:43:27 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 189 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 437 expanded)
%              Number of equality atoms :   70 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f453,f897,f1150])).

fof(f1150,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1143])).

fof(f1143,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f72,f1104])).

fof(f1104,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1065,f101])).

fof(f101,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f89,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f89,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f29,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1065,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f213,f1061])).

fof(f1061,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k2_xboole_0(sK0,X0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f1056,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f1056,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f1055])).

fof(f1055,plain,
    ( r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f1036,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1036,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK0),sK1)
        | r1_xboole_0(X0,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f910,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f910,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f900,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f900,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f448,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f448,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl6_1
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f213,plain,(
    ~ r2_hidden(k1_xboole_0,k3_enumset1(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f208,f52])).

fof(f208,plain,(
    ~ r2_hidden(k1_xboole_0,k3_enumset1(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f99,f99,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f99,plain,(
    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f30,f32])).

fof(f30,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f897,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f894])).

fof(f894,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f48,f892])).

fof(f892,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f891,f52])).

fof(f891,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f890,f101])).

fof(f890,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f534,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f534,plain,
    ( ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f502,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f502,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f486,f32])).

fof(f486,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl6_2 ),
    inference(superposition,[],[f86,f452])).

fof(f452,plain,
    ( k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl6_2
  <=> k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,(
    ! [X0,X1] : ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,X0,X1),sK2) ),
    inference(unit_resulting_resolution,[],[f76,f28,f34])).

fof(f28,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f453,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f109,f450,f446])).

fof(f109,plain,
    ( k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f58,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f59,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f27,f58])).

fof(f27,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:34:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (17450)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (17441)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (17443)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (17439)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (17432)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (17429)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (17431)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (17427)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (17440)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (17430)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (17433)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (17436)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (17455)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (17437)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (17454)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (17451)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (17428)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.55  % (17448)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (17453)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (17457)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (17442)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.56  % (17438)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (17456)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.56  % (17445)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (17434)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (17449)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.56  % (17435)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (17447)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.57  % (17431)Refutation found. Thanks to Tanya!
% 1.41/0.57  % SZS status Theorem for theBenchmark
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f1151,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(avatar_sat_refutation,[],[f453,f897,f1150])).
% 1.41/0.57  fof(f1150,plain,(
% 1.41/0.57    ~spl6_1),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f1143])).
% 1.41/0.57  fof(f1143,plain,(
% 1.41/0.57    $false | ~spl6_1),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f72,f1104])).
% 1.41/0.57  fof(f1104,plain,(
% 1.41/0.57    ~r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl6_1),
% 1.41/0.57    inference(forward_demodulation,[],[f1065,f101])).
% 1.41/0.57  fof(f101,plain,(
% 1.41/0.57    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.41/0.57    inference(superposition,[],[f89,f52])).
% 1.41/0.57  fof(f52,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f1])).
% 1.41/0.57  fof(f1,axiom,(
% 1.41/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.41/0.57  fof(f89,plain,(
% 1.41/0.57    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f29,f33])).
% 1.41/0.57  fof(f33,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.41/0.57    inference(cnf_transformation,[],[f2])).
% 1.41/0.57  fof(f2,axiom,(
% 1.41/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.41/0.57  fof(f29,plain,(
% 1.41/0.57    r1_xboole_0(sK2,sK1)),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  fof(f22,plain,(
% 1.41/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.41/0.57    inference(flattening,[],[f21])).
% 1.41/0.57  fof(f21,plain,(
% 1.41/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.41/0.57    inference(ennf_transformation,[],[f19])).
% 1.41/0.57  fof(f19,negated_conjecture,(
% 1.41/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.41/0.57    inference(negated_conjecture,[],[f18])).
% 1.41/0.57  fof(f18,conjecture,(
% 1.41/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.41/0.57  fof(f1065,plain,(
% 1.41/0.57    ~r2_hidden(k1_xboole_0,k3_enumset1(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | ~spl6_1),
% 1.41/0.57    inference(backward_demodulation,[],[f213,f1061])).
% 1.41/0.57  fof(f1061,plain,(
% 1.41/0.57    ( ! [X0] : (k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k2_xboole_0(sK0,X0))) ) | ~spl6_1),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f1056,f31])).
% 1.41/0.57  fof(f31,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f23])).
% 1.41/0.57  fof(f23,plain,(
% 1.41/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.41/0.57    inference(ennf_transformation,[],[f7])).
% 1.41/0.57  fof(f7,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.41/0.57  fof(f1056,plain,(
% 1.41/0.57    r1_xboole_0(sK1,sK0) | ~spl6_1),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f1055])).
% 1.41/0.57  fof(f1055,plain,(
% 1.41/0.57    r1_xboole_0(sK1,sK0) | r1_xboole_0(sK1,sK0) | ~spl6_1),
% 1.41/0.57    inference(resolution,[],[f1036,f35])).
% 1.41/0.57  fof(f35,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f24])).
% 1.41/0.57  fof(f24,plain,(
% 1.41/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.41/0.57    inference(ennf_transformation,[],[f20])).
% 1.41/0.57  fof(f20,plain,(
% 1.41/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.57    inference(rectify,[],[f3])).
% 1.41/0.57  fof(f3,axiom,(
% 1.41/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.41/0.57  fof(f1036,plain,(
% 1.41/0.57    ( ! [X0] : (~r2_hidden(sK4(X0,sK0),sK1) | r1_xboole_0(X0,sK0)) ) | ~spl6_1),
% 1.41/0.57    inference(resolution,[],[f910,f36])).
% 1.41/0.57  fof(f36,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f24])).
% 1.41/0.57  fof(f910,plain,(
% 1.41/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl6_1),
% 1.41/0.57    inference(resolution,[],[f900,f34])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f24])).
% 1.41/0.57  fof(f900,plain,(
% 1.41/0.57    r1_xboole_0(sK0,sK1) | ~spl6_1),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f448,f32])).
% 1.41/0.57  fof(f32,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f2])).
% 1.41/0.57  fof(f448,plain,(
% 1.41/0.57    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl6_1),
% 1.41/0.57    inference(avatar_component_clause,[],[f446])).
% 1.41/0.57  fof(f446,plain,(
% 1.41/0.57    spl6_1 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.57  fof(f213,plain,(
% 1.41/0.57    ~r2_hidden(k1_xboole_0,k3_enumset1(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))))),
% 1.41/0.57    inference(forward_demodulation,[],[f208,f52])).
% 1.41/0.57  fof(f208,plain,(
% 1.41/0.57    ~r2_hidden(k1_xboole_0,k3_enumset1(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)))),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f99,f99,f99,f77])).
% 1.41/0.57  fof(f77,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.41/0.57    inference(equality_resolution,[],[f63])).
% 1.41/0.57  fof(f63,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.41/0.57    inference(definition_unfolding,[],[f41,f56])).
% 1.41/0.57  fof(f56,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.41/0.57    inference(definition_unfolding,[],[f53,f55])).
% 1.41/0.57  fof(f55,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f12])).
% 1.41/0.57  fof(f12,axiom,(
% 1.41/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.57  fof(f53,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f11])).
% 1.41/0.57  fof(f11,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.57  fof(f41,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.57    inference(cnf_transformation,[],[f25])).
% 1.41/0.57  fof(f25,plain,(
% 1.41/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.41/0.57    inference(ennf_transformation,[],[f8])).
% 1.41/0.57  fof(f8,axiom,(
% 1.41/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.41/0.57  fof(f99,plain,(
% 1.41/0.57    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f30,f32])).
% 1.41/0.57  fof(f30,plain,(
% 1.41/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  fof(f72,plain,(
% 1.41/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 1.41/0.57    inference(equality_resolution,[],[f71])).
% 1.41/0.57  fof(f71,plain,(
% 1.41/0.57    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 1.41/0.57    inference(equality_resolution,[],[f60])).
% 1.41/0.57  fof(f60,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.41/0.57    inference(definition_unfolding,[],[f44,f56])).
% 1.41/0.57  fof(f44,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.57    inference(cnf_transformation,[],[f25])).
% 1.41/0.57  fof(f897,plain,(
% 1.41/0.57    ~spl6_2),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f894])).
% 1.41/0.57  fof(f894,plain,(
% 1.41/0.57    $false | ~spl6_2),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f48,f892])).
% 1.41/0.57  fof(f892,plain,(
% 1.41/0.57    ~r1_tarski(k3_xboole_0(k1_xboole_0,sK0),k1_xboole_0) | ~spl6_2),
% 1.41/0.57    inference(forward_demodulation,[],[f891,f52])).
% 1.41/0.57  fof(f891,plain,(
% 1.41/0.57    ~r1_tarski(k3_xboole_0(sK0,k1_xboole_0),k1_xboole_0) | ~spl6_2),
% 1.41/0.57    inference(forward_demodulation,[],[f890,f101])).
% 1.41/0.57  fof(f890,plain,(
% 1.41/0.57    ~r1_tarski(k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl6_2),
% 1.41/0.57    inference(forward_demodulation,[],[f534,f51])).
% 1.41/0.57  fof(f51,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f4])).
% 1.41/0.57  fof(f4,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.41/0.57  fof(f534,plain,(
% 1.41/0.57    ~r1_tarski(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k1_xboole_0) | ~spl6_2),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f502,f49])).
% 1.41/0.57  fof(f49,plain,(
% 1.41/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.41/0.57    inference(cnf_transformation,[],[f26])).
% 1.41/0.57  fof(f26,plain,(
% 1.41/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.41/0.57    inference(ennf_transformation,[],[f6])).
% 1.41/0.57  fof(f6,axiom,(
% 1.41/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.41/0.57  fof(f502,plain,(
% 1.41/0.57    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl6_2),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f486,f32])).
% 1.41/0.57  fof(f486,plain,(
% 1.41/0.57    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl6_2),
% 1.41/0.57    inference(superposition,[],[f86,f452])).
% 1.41/0.57  fof(f452,plain,(
% 1.41/0.57    k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~spl6_2),
% 1.41/0.57    inference(avatar_component_clause,[],[f450])).
% 1.41/0.57  fof(f450,plain,(
% 1.41/0.57    spl6_2 <=> k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.57  fof(f86,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r1_xboole_0(k3_enumset1(sK3,sK3,sK3,X0,X1),sK2)) )),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f76,f28,f34])).
% 1.41/0.57  fof(f28,plain,(
% 1.41/0.57    r2_hidden(sK3,sK2)),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  fof(f76,plain,(
% 1.41/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.41/0.57    inference(equality_resolution,[],[f75])).
% 1.41/0.57  fof(f75,plain,(
% 1.41/0.57    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.41/0.57    inference(equality_resolution,[],[f62])).
% 1.41/0.57  fof(f62,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.41/0.57    inference(definition_unfolding,[],[f42,f56])).
% 1.41/0.57  fof(f42,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.57    inference(cnf_transformation,[],[f25])).
% 1.41/0.57  fof(f48,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f5])).
% 1.41/0.57  fof(f5,axiom,(
% 1.41/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.41/0.57  fof(f453,plain,(
% 1.41/0.57    spl6_1 | spl6_2),
% 1.41/0.57    inference(avatar_split_clause,[],[f109,f450,f446])).
% 1.41/0.57  fof(f109,plain,(
% 1.41/0.57    k3_xboole_0(sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.41/0.57    inference(resolution,[],[f59,f70])).
% 1.41/0.57  fof(f70,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.41/0.57    inference(definition_unfolding,[],[f45,f58,f58])).
% 1.41/0.57  fof(f58,plain,(
% 1.41/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.41/0.57    inference(definition_unfolding,[],[f50,f57])).
% 1.41/0.57  fof(f57,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.41/0.57    inference(definition_unfolding,[],[f54,f56])).
% 1.41/0.57  fof(f54,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f10])).
% 1.41/0.57  fof(f10,axiom,(
% 1.41/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.57  fof(f50,plain,(
% 1.41/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f9])).
% 1.41/0.57  fof(f9,axiom,(
% 1.41/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.57  fof(f45,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f16])).
% 1.41/0.57  fof(f16,axiom,(
% 1.41/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.41/0.57  fof(f59,plain,(
% 1.41/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 1.41/0.57    inference(definition_unfolding,[],[f27,f58])).
% 1.41/0.57  fof(f27,plain,(
% 1.41/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  % SZS output end Proof for theBenchmark
% 1.41/0.57  % (17431)------------------------------
% 1.41/0.57  % (17431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (17431)Termination reason: Refutation
% 1.41/0.57  
% 1.41/0.57  % (17431)Memory used [KB]: 6780
% 1.41/0.57  % (17431)Time elapsed: 0.158 s
% 1.41/0.57  % (17431)------------------------------
% 1.41/0.57  % (17431)------------------------------
% 1.62/0.57  % (17452)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.62/0.58  % (17444)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.62/0.58  % (17444)Refutation not found, incomplete strategy% (17444)------------------------------
% 1.62/0.58  % (17444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (17444)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (17444)Memory used [KB]: 10746
% 1.62/0.58  % (17444)Time elapsed: 0.168 s
% 1.62/0.58  % (17444)------------------------------
% 1.62/0.58  % (17444)------------------------------
% 1.62/0.59  % (17423)Success in time 0.229 s
%------------------------------------------------------------------------------
