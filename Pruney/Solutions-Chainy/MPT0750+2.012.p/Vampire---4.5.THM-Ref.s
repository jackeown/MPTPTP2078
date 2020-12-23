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
% DateTime   : Thu Dec  3 12:55:41 EST 2020

% Result     : Theorem 13.76s
% Output     : Refutation 13.76s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 467 expanded)
%              Number of leaves         :   42 ( 173 expanded)
%              Depth                    :   18
%              Number of atoms          :  739 (1834 expanded)
%              Number of equality atoms :   46 ( 112 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11790,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f127,f135,f162,f292,f561,f731,f835,f1966,f2965,f3886,f4865,f5002,f5441,f5457,f6083,f6088,f6335,f7932,f10653,f10780,f11789])).

fof(f11789,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89
    | ~ spl8_148
    | ~ spl8_150 ),
    inference(avatar_contradiction_clause,[],[f11788])).

fof(f11788,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89
    | ~ spl8_148
    | ~ spl8_150 ),
    inference(subsumption_resolution,[],[f11784,f11099])).

fof(f11099,plain,
    ( r1_tarski(sK7(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89
    | ~ spl8_148 ),
    inference(unit_resulting_resolution,[],[f10652,f6990])).

fof(f6990,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89 ),
    inference(subsumption_resolution,[],[f6989,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v3_ordinal1(X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f82,f117])).

fof(f117,plain,
    ( v3_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f6989,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r1_tarski(X0,sK1)
        | ~ v3_ordinal1(X0) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89 ),
    inference(resolution,[],[f6792,f6068])).

fof(f6068,plain,
    ( ! [X4] :
        ( ~ r1_ordinal1(X4,sK1)
        | r1_tarski(X4,sK1)
        | ~ v3_ordinal1(X4) )
    | ~ spl8_3 ),
    inference(resolution,[],[f126,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f126,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f6792,plain,
    ( ! [X7] :
        ( r1_ordinal1(X7,sK1)
        | ~ r2_hidden(X7,sK0) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89 ),
    inference(subsumption_resolution,[],[f6664,f149])).

fof(f6664,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r1_ordinal1(X7,sK1)
        | ~ v3_ordinal1(X7) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89 ),
    inference(backward_demodulation,[],[f6071,f6588])).

fof(f6588,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_9
    | spl8_88
    | spl8_89 ),
    inference(subsumption_resolution,[],[f6587,f267])).

fof(f267,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl8_9
  <=> v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f6587,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | spl8_88
    | spl8_89 ),
    inference(subsumption_resolution,[],[f6586,f6087])).

fof(f6087,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl8_88 ),
    inference(avatar_component_clause,[],[f6085])).

fof(f6085,plain,
    ( spl8_88
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f6586,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | spl8_89 ),
    inference(subsumption_resolution,[],[f6585,f117])).

fof(f6585,plain,
    ( ~ v3_ordinal1(sK0)
    | r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3
    | spl8_89 ),
    inference(subsumption_resolution,[],[f6555,f6548])).

fof(f6548,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_3
    | spl8_89 ),
    inference(unit_resulting_resolution,[],[f117,f126,f6334,f83])).

fof(f6334,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl8_89 ),
    inference(avatar_component_clause,[],[f6332])).

fof(f6332,plain,
    ( spl8_89
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f6555,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f6071,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | r2_hidden(X0,sK0)
        | sK0 = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f71,f117])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | X0 = X1
      | r2_hidden(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f6071,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,k2_xboole_0(sK1,k1_tarski(sK1)))
        | r1_ordinal1(X7,sK1)
        | ~ v3_ordinal1(X7) )
    | ~ spl8_3 ),
    inference(resolution,[],[f126,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f10652,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_148 ),
    inference(avatar_component_clause,[],[f10650])).

fof(f10650,plain,
    ( spl8_148
  <=> r2_hidden(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f11784,plain,
    ( ~ r1_tarski(sK7(sK0,sK1),sK1)
    | ~ spl8_150 ),
    inference(resolution,[],[f10779,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f10779,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_150 ),
    inference(avatar_component_clause,[],[f10777])).

fof(f10777,plain,
    ( spl8_150
  <=> r2_hidden(sK1,sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f10780,plain,
    ( spl8_150
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f8173,f155,f132,f10777])).

fof(f132,plain,
    ( spl8_4
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f155,plain,
    ( spl8_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f8173,plain,
    ( r2_hidden(sK1,sK7(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f156,f7935])).

fof(f7935,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(X1,sK7(sK0,X1)) )
    | ~ spl8_4 ),
    inference(superposition,[],[f112,f133])).

fof(f133,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f112,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k3_tarski(X0))
      | r2_hidden(X5,sK7(X0,X5)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK7(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK5(X0,X1),X3) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ( r2_hidden(sK6(X0,X1),X0)
              & r2_hidden(sK5(X0,X1),sK6(X0,X1)) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK7(X0,X5),X0)
                & r2_hidden(X5,sK7(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f53,f56,f55,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK5(X0,X1),X3) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK5(X0,X1),X4) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f156,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f10653,plain,
    ( spl8_148
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f8165,f155,f132,f10650])).

fof(f8165,plain,
    ( r2_hidden(sK7(sK0,sK1),sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f156,f7934])).

fof(f7934,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_4 ),
    inference(superposition,[],[f111,f133])).

fof(f111,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k3_tarski(X0))
      | r2_hidden(sK7(X0,X5),X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7932,plain,
    ( spl8_4
    | ~ spl8_1
    | ~ spl8_11
    | spl8_36
    | spl8_59 ),
    inference(avatar_split_clause,[],[f5463,f3130,f1963,f289,f115,f132])).

fof(f289,plain,
    ( spl8_11
  <=> v3_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f1963,plain,
    ( spl8_36
  <=> r2_hidden(k3_tarski(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f3130,plain,
    ( spl8_59
  <=> r2_hidden(sK7(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f5463,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_1
    | ~ spl8_11
    | spl8_36
    | spl8_59 ),
    inference(subsumption_resolution,[],[f5462,f3131])).

fof(f3131,plain,
    ( ~ r2_hidden(sK7(sK0,sK0),sK0)
    | spl8_59 ),
    inference(avatar_component_clause,[],[f3130])).

fof(f5462,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_hidden(sK7(sK0,sK0),sK0)
    | ~ spl8_1
    | ~ spl8_11
    | spl8_36 ),
    inference(subsumption_resolution,[],[f4868,f2706])).

fof(f2706,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_11
    | spl8_36 ),
    inference(unit_resulting_resolution,[],[f291,f1965,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ v3_ordinal1(X2)
      | r2_hidden(X2,sK4(X0))
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK4(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK4(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK4(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK4(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f1965,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK4(sK0))
    | spl8_36 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f291,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f289])).

fof(f4868,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_hidden(k3_tarski(sK0),sK0)
    | r2_hidden(sK7(sK0,sK0),sK0)
    | ~ spl8_1
    | ~ spl8_11 ),
    inference(resolution,[],[f481,f291])).

fof(f481,plain,
    ( ! [X4] :
        ( ~ v3_ordinal1(k3_tarski(X4))
        | sK0 = k3_tarski(X4)
        | r2_hidden(k3_tarski(X4),sK0)
        | r2_hidden(sK7(X4,sK0),X4) )
    | ~ spl8_1 ),
    inference(resolution,[],[f209,f111])).

fof(f6335,plain,
    ( ~ spl8_89
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f6121,f155,f6332])).

fof(f6121,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f156,f97])).

fof(f6088,plain,
    ( ~ spl8_88
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f5997,f120,f6085])).

fof(f120,plain,
    ( spl8_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f5997,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f98,f121])).

fof(f121,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f98,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f64,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
        & r2_hidden(sK1,sK0)
        & v3_ordinal1(sK1) )
      | ~ v4_ordinal1(sK0) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK0)
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK0) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK0)
            & r2_hidden(X1,sK0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK0)
            | ~ r2_hidden(X2,sK0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f6083,plain,
    ( spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f5996,f120,f155])).

fof(f5996,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f63,f121])).

fof(f63,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f5457,plain,
    ( ~ spl8_2
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f5456])).

fof(f5456,plain,
    ( $false
    | ~ spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f121,f851])).

fof(f851,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f134,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v4_ordinal1(X0)
      | k3_tarski(X0) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f134,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f5441,plain,
    ( ~ spl8_1
    | ~ spl8_73
    | spl8_80
    | ~ spl8_83 ),
    inference(avatar_contradiction_clause,[],[f5440])).

fof(f5440,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_73
    | spl8_80
    | ~ spl8_83 ),
    inference(subsumption_resolution,[],[f5436,f5001])).

fof(f5001,plain,
    ( r1_ordinal1(sK7(sK0,sK0),sK0)
    | ~ spl8_83 ),
    inference(avatar_component_clause,[],[f4999])).

fof(f4999,plain,
    ( spl8_83
  <=> r1_ordinal1(sK7(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f5436,plain,
    ( ~ r1_ordinal1(sK7(sK0,sK0),sK0)
    | ~ spl8_1
    | ~ spl8_73
    | spl8_80 ),
    inference(unit_resulting_resolution,[],[f3885,f4864,f186])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(X0,sK0)
        | r1_tarski(X0,sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f83,f117])).

fof(f4864,plain,
    ( ~ r1_tarski(sK7(sK0,sK0),sK0)
    | spl8_80 ),
    inference(avatar_component_clause,[],[f4862])).

fof(f4862,plain,
    ( spl8_80
  <=> r1_tarski(sK7(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f3885,plain,
    ( v3_ordinal1(sK7(sK0,sK0))
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f3883])).

fof(f3883,plain,
    ( spl8_73
  <=> v3_ordinal1(sK7(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f5002,plain,
    ( spl8_83
    | ~ spl8_1
    | ~ spl8_59 ),
    inference(avatar_split_clause,[],[f3777,f3130,f115,f4999])).

fof(f3777,plain,
    ( r1_ordinal1(sK7(sK0,sK0),sK0)
    | ~ spl8_1
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f3132,f526])).

fof(f526,plain,
    ( ! [X1] :
        ( r1_ordinal1(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f520,f149])).

fof(f520,plain,
    ( ! [X1] :
        ( r1_ordinal1(X1,sK0)
        | ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f219,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f95,f67])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,k1_tarski(sK0)))
        | r1_ordinal1(X0,sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f104,f117])).

fof(f3132,plain,
    ( r2_hidden(sK7(sK0,sK0),sK0)
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f3130])).

fof(f4865,plain,
    ( ~ spl8_80
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f3626,f2962,f4862])).

fof(f2962,plain,
    ( spl8_58
  <=> r2_hidden(sK0,sK7(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f3626,plain,
    ( ~ r1_tarski(sK7(sK0,sK0),sK0)
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f2964,f97])).

fof(f2964,plain,
    ( r2_hidden(sK0,sK7(sK0,sK0))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f2962])).

fof(f3886,plain,
    ( spl8_73
    | ~ spl8_1
    | ~ spl8_59 ),
    inference(avatar_split_clause,[],[f3778,f3130,f115,f3883])).

fof(f3778,plain,
    ( v3_ordinal1(sK7(sK0,sK0))
    | ~ spl8_1
    | ~ spl8_59 ),
    inference(unit_resulting_resolution,[],[f117,f3132,f82])).

fof(f2965,plain,
    ( spl8_58
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f1153,f728,f2962])).

fof(f728,plain,
    ( spl8_17
  <=> r2_hidden(sK0,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f1153,plain,
    ( r2_hidden(sK0,sK7(sK0,sK0))
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f730,f112])).

fof(f730,plain,
    ( r2_hidden(sK0,k3_tarski(sK0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f728])).

fof(f1966,plain,
    ( ~ spl8_36
    | spl8_16 ),
    inference(avatar_split_clause,[],[f619,f558,f1963])).

fof(f558,plain,
    ( spl8_16
  <=> r2_hidden(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f619,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK4(sK0))
    | spl8_16 ),
    inference(unit_resulting_resolution,[],[f560,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK4(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f560,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f558])).

fof(f835,plain,
    ( ~ spl8_3
    | spl8_9 ),
    inference(avatar_split_clause,[],[f287,f266,f124])).

fof(f287,plain,
    ( ~ v3_ordinal1(sK1)
    | spl8_9 ),
    inference(resolution,[],[f268,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f68,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f268,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f266])).

fof(f731,plain,
    ( spl8_17
    | ~ spl8_1
    | spl8_4
    | ~ spl8_11
    | spl8_16 ),
    inference(avatar_split_clause,[],[f616,f558,f289,f132,f115,f728])).

fof(f616,plain,
    ( r2_hidden(sK0,k3_tarski(sK0))
    | ~ spl8_1
    | spl8_4
    | ~ spl8_11
    | spl8_16 ),
    inference(unit_resulting_resolution,[],[f117,f291,f134,f560,f71])).

fof(f561,plain,
    ( ~ spl8_16
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f550,f160,f115,f558])).

fof(f160,plain,
    ( spl8_6
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f550,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f137,f101,f200])).

fof(f200,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,sK0)
        | ~ r2_hidden(X7,k2_xboole_0(X8,k1_tarski(X8)))
        | r2_hidden(X7,k3_tarski(sK0)) )
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(resolution,[],[f110,f163])).

fof(f163,plain,
    ( ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f161,f149])).

fof(f161,plain,
    ( ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f110,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(X6,X0)
      | r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f101,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f66,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f137,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(unit_resulting_resolution,[],[f108,f97])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f292,plain,
    ( spl8_11
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f275,f115,f289])).

fof(f275,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f272,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(X0))
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(f272,plain,
    ( v3_ordinal1(sK2(sK0))
    | v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_1 ),
    inference(resolution,[],[f149,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f162,plain,
    ( spl8_2
    | spl8_6 ),
    inference(avatar_split_clause,[],[f99,f160,f120])).

fof(f99,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f61,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f135,plain,
    ( ~ spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f128,f120,f132])).

fof(f128,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f127,plain,
    ( ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f62,f124,f120])).

fof(f62,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f118,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f60,f115])).

fof(f60,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (21343)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (21362)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (21347)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (21354)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (21370)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (21352)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (21361)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (21350)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (21344)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (21358)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (21345)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (21368)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (21371)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (21359)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (21371)Refutation not found, incomplete strategy% (21371)------------------------------
% 0.22/0.55  % (21371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21371)Memory used [KB]: 10746
% 0.22/0.55  % (21371)Time elapsed: 0.139 s
% 0.22/0.55  % (21371)------------------------------
% 0.22/0.55  % (21371)------------------------------
% 0.22/0.55  % (21359)Refutation not found, incomplete strategy% (21359)------------------------------
% 0.22/0.55  % (21359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21359)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21359)Memory used [KB]: 10618
% 0.22/0.55  % (21359)Time elapsed: 0.138 s
% 0.22/0.55  % (21359)------------------------------
% 0.22/0.55  % (21359)------------------------------
% 0.22/0.55  % (21360)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (21346)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (21348)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (21363)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (21355)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (21353)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (21367)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (21364)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (21366)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (21349)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (21365)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (21372)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (21369)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (21351)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (21357)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (21356)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.58  % (21353)Refutation not found, incomplete strategy% (21353)------------------------------
% 0.22/0.58  % (21353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (21353)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (21353)Memory used [KB]: 10746
% 0.22/0.58  % (21353)Time elapsed: 0.166 s
% 0.22/0.58  % (21353)------------------------------
% 0.22/0.58  % (21353)------------------------------
% 2.16/0.68  % (21373)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.69  % (21374)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.73  % (21375)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.73  % (21346)Refutation not found, incomplete strategy% (21346)------------------------------
% 2.16/0.73  % (21346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.73  % (21346)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.73  
% 2.16/0.73  % (21346)Memory used [KB]: 6140
% 2.16/0.73  % (21346)Time elapsed: 0.300 s
% 2.16/0.73  % (21346)------------------------------
% 2.16/0.73  % (21346)------------------------------
% 3.27/0.82  % (21345)Time limit reached!
% 3.27/0.82  % (21345)------------------------------
% 3.27/0.82  % (21345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.82  % (21345)Termination reason: Time limit
% 3.27/0.82  % (21345)Termination phase: Saturation
% 3.27/0.82  
% 3.27/0.82  % (21345)Memory used [KB]: 6524
% 3.27/0.82  % (21345)Time elapsed: 0.404 s
% 3.27/0.82  % (21345)------------------------------
% 3.27/0.82  % (21345)------------------------------
% 3.27/0.84  % (21367)Time limit reached!
% 3.27/0.84  % (21367)------------------------------
% 3.27/0.84  % (21367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.84  % (21367)Termination reason: Time limit
% 3.27/0.84  
% 3.27/0.84  % (21367)Memory used [KB]: 12281
% 3.27/0.84  % (21367)Time elapsed: 0.426 s
% 3.27/0.84  % (21367)------------------------------
% 3.27/0.84  % (21367)------------------------------
% 3.76/0.86  % (21376)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.04/0.91  % (21372)Time limit reached!
% 4.04/0.91  % (21372)------------------------------
% 4.04/0.91  % (21372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.92  % (21372)Termination reason: Time limit
% 4.04/0.92  % (21372)Termination phase: Saturation
% 4.04/0.92  
% 4.04/0.92  % (21372)Memory used [KB]: 2302
% 4.04/0.92  % (21372)Time elapsed: 0.500 s
% 4.04/0.92  % (21372)------------------------------
% 4.04/0.92  % (21372)------------------------------
% 4.04/0.94  % (21349)Time limit reached!
% 4.04/0.94  % (21349)------------------------------
% 4.04/0.94  % (21349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.94  % (21349)Termination reason: Time limit
% 4.36/0.94  % (21349)Termination phase: Saturation
% 4.36/0.94  
% 4.36/0.94  % (21349)Memory used [KB]: 14456
% 4.36/0.94  % (21349)Time elapsed: 0.500 s
% 4.36/0.94  % (21349)------------------------------
% 4.36/0.94  % (21349)------------------------------
% 4.36/0.97  % (21357)Time limit reached!
% 4.36/0.97  % (21357)------------------------------
% 4.36/0.97  % (21357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.97  % (21357)Termination reason: Time limit
% 4.36/0.97  
% 4.36/0.97  % (21357)Memory used [KB]: 3837
% 4.36/0.97  % (21357)Time elapsed: 0.523 s
% 4.36/0.97  % (21357)------------------------------
% 4.36/0.97  % (21357)------------------------------
% 4.36/0.99  % (21377)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.36/0.99  % (21377)Refutation not found, incomplete strategy% (21377)------------------------------
% 4.36/0.99  % (21377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.99  % (21377)Termination reason: Refutation not found, incomplete strategy
% 4.36/0.99  
% 4.36/0.99  % (21377)Memory used [KB]: 10746
% 4.36/0.99  % (21377)Time elapsed: 0.137 s
% 4.36/0.99  % (21377)------------------------------
% 4.36/0.99  % (21377)------------------------------
% 4.36/0.99  % (21378)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.01/1.04  % (21350)Time limit reached!
% 5.01/1.04  % (21350)------------------------------
% 5.01/1.04  % (21350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.04  % (21350)Termination reason: Time limit
% 5.01/1.04  % (21350)Termination phase: Saturation
% 5.01/1.04  
% 5.01/1.04  % (21350)Memory used [KB]: 4989
% 5.01/1.04  % (21350)Time elapsed: 0.600 s
% 5.01/1.04  % (21350)------------------------------
% 5.01/1.04  % (21350)------------------------------
% 5.01/1.07  % (21379)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.29/1.11  % (21380)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.29/1.12  % (21381)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.29/1.13  % (21382)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 5.29/1.14  % (21383)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.75/1.24  % (21344)Time limit reached!
% 6.75/1.24  % (21344)------------------------------
% 6.75/1.24  % (21344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.89/1.24  % (21344)Termination reason: Time limit
% 6.89/1.24  % (21344)Termination phase: Saturation
% 6.89/1.24  
% 6.89/1.24  % (21344)Memory used [KB]: 6780
% 6.89/1.24  % (21344)Time elapsed: 0.800 s
% 6.89/1.24  % (21344)------------------------------
% 6.89/1.24  % (21344)------------------------------
% 7.46/1.35  % (21384)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 7.88/1.43  % (21370)Time limit reached!
% 7.88/1.43  % (21370)------------------------------
% 7.88/1.43  % (21370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.43  % (21370)Termination reason: Time limit
% 7.88/1.43  
% 7.88/1.43  % (21370)Memory used [KB]: 9978
% 7.88/1.43  % (21370)Time elapsed: 1.021 s
% 7.88/1.43  % (21370)------------------------------
% 7.88/1.43  % (21370)------------------------------
% 7.88/1.44  % (21355)Time limit reached!
% 7.88/1.44  % (21355)------------------------------
% 7.88/1.44  % (21355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.44  % (21355)Termination reason: Time limit
% 7.88/1.44  
% 7.88/1.44  % (21355)Memory used [KB]: 15095
% 7.88/1.44  % (21355)Time elapsed: 1.031 s
% 7.88/1.44  % (21355)------------------------------
% 7.88/1.44  % (21355)------------------------------
% 8.51/1.46  % (21375)Time limit reached!
% 8.51/1.46  % (21375)------------------------------
% 8.51/1.46  % (21375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.51/1.46  % (21375)Termination reason: Time limit
% 8.51/1.46  
% 8.51/1.46  % (21375)Memory used [KB]: 12537
% 8.51/1.46  % (21375)Time elapsed: 0.819 s
% 8.51/1.46  % (21375)------------------------------
% 8.51/1.46  % (21375)------------------------------
% 9.19/1.56  % (21386)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.19/1.57  % (21387)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 9.19/1.58  % (21385)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 9.19/1.60  % (21379)Time limit reached!
% 9.19/1.60  % (21379)------------------------------
% 9.19/1.60  % (21379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.19/1.60  % (21379)Termination reason: Time limit
% 9.19/1.60  % (21379)Termination phase: Saturation
% 9.19/1.60  
% 9.19/1.60  % (21379)Memory used [KB]: 16375
% 9.19/1.60  % (21379)Time elapsed: 0.600 s
% 9.19/1.60  % (21379)------------------------------
% 9.19/1.60  % (21379)------------------------------
% 9.66/1.64  % (21343)Time limit reached!
% 9.66/1.64  % (21343)------------------------------
% 9.66/1.64  % (21343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.66/1.64  % (21343)Termination reason: Time limit
% 9.66/1.64  
% 9.66/1.64  % (21343)Memory used [KB]: 4861
% 9.66/1.64  % (21343)Time elapsed: 1.216 s
% 9.66/1.64  % (21343)------------------------------
% 9.66/1.64  % (21343)------------------------------
% 10.38/1.73  % (21348)Time limit reached!
% 10.38/1.73  % (21348)------------------------------
% 10.38/1.73  % (21348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.38/1.73  % (21348)Termination reason: Time limit
% 10.38/1.73  
% 10.38/1.73  % (21348)Memory used [KB]: 7931
% 10.38/1.73  % (21348)Time elapsed: 1.317 s
% 10.38/1.73  % (21348)------------------------------
% 10.38/1.73  % (21348)------------------------------
% 10.38/1.73  % (21387)Refutation not found, incomplete strategy% (21387)------------------------------
% 10.38/1.73  % (21387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.38/1.73  % (21387)Termination reason: Refutation not found, incomplete strategy
% 10.38/1.73  
% 10.38/1.73  % (21387)Memory used [KB]: 6268
% 10.38/1.73  % (21387)Time elapsed: 0.228 s
% 10.38/1.73  % (21387)------------------------------
% 10.38/1.73  % (21387)------------------------------
% 10.38/1.74  % (21388)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.21/1.81  % (21389)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 11.47/1.83  % (21382)Time limit reached!
% 11.47/1.83  % (21382)------------------------------
% 11.47/1.83  % (21382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.47/1.83  % (21382)Termination reason: Time limit
% 11.47/1.83  % (21382)Termination phase: Saturation
% 11.47/1.83  
% 11.47/1.83  % (21382)Memory used [KB]: 13816
% 11.47/1.83  % (21382)Time elapsed: 0.800 s
% 11.47/1.83  % (21382)------------------------------
% 11.47/1.83  % (21382)------------------------------
% 11.47/1.85  % (21390)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 11.47/1.87  % (21391)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 12.20/1.91  % (21386)Time limit reached!
% 12.20/1.91  % (21386)------------------------------
% 12.20/1.91  % (21386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.20/1.92  % (21386)Termination reason: Time limit
% 12.20/1.92  
% 12.20/1.92  % (21386)Memory used [KB]: 12665
% 12.20/1.92  % (21386)Time elapsed: 0.415 s
% 12.20/1.92  % (21386)------------------------------
% 12.20/1.92  % (21386)------------------------------
% 12.66/1.99  % (21392)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 12.66/2.01  % (21369)Time limit reached!
% 12.66/2.01  % (21369)------------------------------
% 12.66/2.01  % (21369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.66/2.01  % (21369)Termination reason: Time limit
% 12.66/2.01  % (21369)Termination phase: Saturation
% 12.66/2.01  
% 12.66/2.01  % (21369)Memory used [KB]: 13944
% 12.66/2.01  % (21369)Time elapsed: 1.600 s
% 12.66/2.01  % (21369)------------------------------
% 12.66/2.01  % (21369)------------------------------
% 12.66/2.02  % (21395)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 13.29/2.07  % (21388)Time limit reached!
% 13.29/2.07  % (21388)------------------------------
% 13.29/2.07  % (21388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.29/2.08  % (21388)Termination reason: Time limit
% 13.29/2.08  
% 13.29/2.08  % (21388)Memory used [KB]: 6780
% 13.29/2.08  % (21388)Time elapsed: 0.431 s
% 13.29/2.08  % (21388)------------------------------
% 13.29/2.08  % (21388)------------------------------
% 13.76/2.13  % (21363)Refutation found. Thanks to Tanya!
% 13.76/2.13  % SZS status Theorem for theBenchmark
% 13.76/2.13  % SZS output start Proof for theBenchmark
% 13.76/2.13  fof(f11790,plain,(
% 13.76/2.13    $false),
% 13.76/2.13    inference(avatar_sat_refutation,[],[f118,f127,f135,f162,f292,f561,f731,f835,f1966,f2965,f3886,f4865,f5002,f5441,f5457,f6083,f6088,f6335,f7932,f10653,f10780,f11789])).
% 13.76/2.13  fof(f11789,plain,(
% 13.76/2.13    ~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89 | ~spl8_148 | ~spl8_150),
% 13.76/2.13    inference(avatar_contradiction_clause,[],[f11788])).
% 13.76/2.13  fof(f11788,plain,(
% 13.76/2.13    $false | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89 | ~spl8_148 | ~spl8_150)),
% 13.76/2.13    inference(subsumption_resolution,[],[f11784,f11099])).
% 13.76/2.13  fof(f11099,plain,(
% 13.76/2.13    r1_tarski(sK7(sK0,sK1),sK1) | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89 | ~spl8_148)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f10652,f6990])).
% 13.76/2.13  fof(f6990,plain,(
% 13.76/2.13    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK1)) ) | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89)),
% 13.76/2.13    inference(subsumption_resolution,[],[f6989,f149])).
% 13.76/2.13  fof(f149,plain,(
% 13.76/2.13    ( ! [X0] : (~r2_hidden(X0,sK0) | v3_ordinal1(X0)) ) | ~spl8_1),
% 13.76/2.13    inference(resolution,[],[f82,f117])).
% 13.76/2.13  fof(f117,plain,(
% 13.76/2.13    v3_ordinal1(sK0) | ~spl8_1),
% 13.76/2.13    inference(avatar_component_clause,[],[f115])).
% 13.76/2.13  fof(f115,plain,(
% 13.76/2.13    spl8_1 <=> v3_ordinal1(sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 13.76/2.13  fof(f82,plain,(
% 13.76/2.13    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | v3_ordinal1(X0)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f29])).
% 13.76/2.13  fof(f29,plain,(
% 13.76/2.13    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 13.76/2.13    inference(flattening,[],[f28])).
% 13.76/2.13  fof(f28,plain,(
% 13.76/2.13    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 13.76/2.13    inference(ennf_transformation,[],[f10])).
% 13.76/2.13  fof(f10,axiom,(
% 13.76/2.13    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 13.76/2.13  fof(f6989,plain,(
% 13.76/2.13    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) ) | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89)),
% 13.76/2.13    inference(resolution,[],[f6792,f6068])).
% 13.76/2.13  fof(f6068,plain,(
% 13.76/2.13    ( ! [X4] : (~r1_ordinal1(X4,sK1) | r1_tarski(X4,sK1) | ~v3_ordinal1(X4)) ) | ~spl8_3),
% 13.76/2.13    inference(resolution,[],[f126,f83])).
% 13.76/2.13  fof(f83,plain,(
% 13.76/2.13    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f49])).
% 13.76/2.13  fof(f49,plain,(
% 13.76/2.13    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 13.76/2.13    inference(nnf_transformation,[],[f31])).
% 13.76/2.13  fof(f31,plain,(
% 13.76/2.13    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 13.76/2.13    inference(flattening,[],[f30])).
% 13.76/2.13  fof(f30,plain,(
% 13.76/2.13    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 13.76/2.13    inference(ennf_transformation,[],[f5])).
% 13.76/2.13  fof(f5,axiom,(
% 13.76/2.13    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 13.76/2.13  fof(f126,plain,(
% 13.76/2.13    v3_ordinal1(sK1) | ~spl8_3),
% 13.76/2.13    inference(avatar_component_clause,[],[f124])).
% 13.76/2.13  fof(f124,plain,(
% 13.76/2.13    spl8_3 <=> v3_ordinal1(sK1)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 13.76/2.13  fof(f6792,plain,(
% 13.76/2.13    ( ! [X7] : (r1_ordinal1(X7,sK1) | ~r2_hidden(X7,sK0)) ) | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89)),
% 13.76/2.13    inference(subsumption_resolution,[],[f6664,f149])).
% 13.76/2.13  fof(f6664,plain,(
% 13.76/2.13    ( ! [X7] : (~r2_hidden(X7,sK0) | r1_ordinal1(X7,sK1) | ~v3_ordinal1(X7)) ) | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89)),
% 13.76/2.13    inference(backward_demodulation,[],[f6071,f6588])).
% 13.76/2.13  fof(f6588,plain,(
% 13.76/2.13    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (~spl8_1 | ~spl8_3 | ~spl8_9 | spl8_88 | spl8_89)),
% 13.76/2.13    inference(subsumption_resolution,[],[f6587,f267])).
% 13.76/2.13  fof(f267,plain,(
% 13.76/2.13    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl8_9),
% 13.76/2.13    inference(avatar_component_clause,[],[f266])).
% 13.76/2.13  fof(f266,plain,(
% 13.76/2.13    spl8_9 <=> v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 13.76/2.13  fof(f6587,plain,(
% 13.76/2.13    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3 | spl8_88 | spl8_89)),
% 13.76/2.13    inference(subsumption_resolution,[],[f6586,f6087])).
% 13.76/2.13  fof(f6087,plain,(
% 13.76/2.13    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl8_88),
% 13.76/2.13    inference(avatar_component_clause,[],[f6085])).
% 13.76/2.13  fof(f6085,plain,(
% 13.76/2.13    spl8_88 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 13.76/2.13  fof(f6586,plain,(
% 13.76/2.13    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3 | spl8_89)),
% 13.76/2.13    inference(subsumption_resolution,[],[f6585,f117])).
% 13.76/2.13  fof(f6585,plain,(
% 13.76/2.13    ~v3_ordinal1(sK0) | r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3 | spl8_89)),
% 13.76/2.13    inference(subsumption_resolution,[],[f6555,f6548])).
% 13.76/2.13  fof(f6548,plain,(
% 13.76/2.13    ~r1_ordinal1(sK0,sK1) | (~spl8_1 | ~spl8_3 | spl8_89)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f117,f126,f6334,f83])).
% 13.76/2.13  fof(f6334,plain,(
% 13.76/2.13    ~r1_tarski(sK0,sK1) | spl8_89),
% 13.76/2.13    inference(avatar_component_clause,[],[f6332])).
% 13.76/2.13  fof(f6332,plain,(
% 13.76/2.13    spl8_89 <=> r1_tarski(sK0,sK1)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 13.76/2.13  fof(f6555,plain,(
% 13.76/2.13    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | (~spl8_1 | ~spl8_3)),
% 13.76/2.13    inference(resolution,[],[f6071,f209])).
% 13.76/2.13  fof(f209,plain,(
% 13.76/2.13    ( ! [X0] : (r2_hidden(sK0,X0) | r2_hidden(X0,sK0) | sK0 = X0 | ~v3_ordinal1(X0)) ) | ~spl8_1),
% 13.76/2.13    inference(resolution,[],[f71,f117])).
% 13.76/2.13  fof(f71,plain,(
% 13.76/2.13    ( ! [X0,X1] : (~v3_ordinal1(X1) | X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f24])).
% 13.76/2.13  fof(f24,plain,(
% 13.76/2.13    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 13.76/2.13    inference(flattening,[],[f23])).
% 13.76/2.13  fof(f23,plain,(
% 13.76/2.13    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 13.76/2.13    inference(ennf_transformation,[],[f11])).
% 13.76/2.13  fof(f11,axiom,(
% 13.76/2.13    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 13.76/2.13  fof(f6071,plain,(
% 13.76/2.13    ( ! [X7] : (~r2_hidden(X7,k2_xboole_0(sK1,k1_tarski(sK1))) | r1_ordinal1(X7,sK1) | ~v3_ordinal1(X7)) ) | ~spl8_3),
% 13.76/2.13    inference(resolution,[],[f126,f104])).
% 13.76/2.13  fof(f104,plain,(
% 13.76/2.13    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 13.76/2.13    inference(definition_unfolding,[],[f69,f67])).
% 13.76/2.13  fof(f67,plain,(
% 13.76/2.13    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 13.76/2.13    inference(cnf_transformation,[],[f3])).
% 13.76/2.13  fof(f3,axiom,(
% 13.76/2.13    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 13.76/2.13  fof(f69,plain,(
% 13.76/2.13    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f39])).
% 13.76/2.13  fof(f39,plain,(
% 13.76/2.13    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 13.76/2.13    inference(nnf_transformation,[],[f22])).
% 13.76/2.13  fof(f22,plain,(
% 13.76/2.13    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 13.76/2.13    inference(ennf_transformation,[],[f13])).
% 13.76/2.13  fof(f13,axiom,(
% 13.76/2.13    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 13.76/2.13  fof(f10652,plain,(
% 13.76/2.13    r2_hidden(sK7(sK0,sK1),sK0) | ~spl8_148),
% 13.76/2.13    inference(avatar_component_clause,[],[f10650])).
% 13.76/2.13  fof(f10650,plain,(
% 13.76/2.13    spl8_148 <=> r2_hidden(sK7(sK0,sK1),sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).
% 13.76/2.13  fof(f11784,plain,(
% 13.76/2.13    ~r1_tarski(sK7(sK0,sK1),sK1) | ~spl8_150),
% 13.76/2.13    inference(resolution,[],[f10779,f97])).
% 13.76/2.13  fof(f97,plain,(
% 13.76/2.13    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f32])).
% 13.76/2.13  fof(f32,plain,(
% 13.76/2.13    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 13.76/2.13    inference(ennf_transformation,[],[f16])).
% 13.76/2.13  fof(f16,axiom,(
% 13.76/2.13    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 13.76/2.13  fof(f10779,plain,(
% 13.76/2.13    r2_hidden(sK1,sK7(sK0,sK1)) | ~spl8_150),
% 13.76/2.13    inference(avatar_component_clause,[],[f10777])).
% 13.76/2.13  fof(f10777,plain,(
% 13.76/2.13    spl8_150 <=> r2_hidden(sK1,sK7(sK0,sK1))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).
% 13.76/2.13  fof(f10780,plain,(
% 13.76/2.13    spl8_150 | ~spl8_4 | ~spl8_5),
% 13.76/2.13    inference(avatar_split_clause,[],[f8173,f155,f132,f10777])).
% 13.76/2.13  fof(f132,plain,(
% 13.76/2.13    spl8_4 <=> sK0 = k3_tarski(sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 13.76/2.13  fof(f155,plain,(
% 13.76/2.13    spl8_5 <=> r2_hidden(sK1,sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 13.76/2.13  fof(f8173,plain,(
% 13.76/2.13    r2_hidden(sK1,sK7(sK0,sK1)) | (~spl8_4 | ~spl8_5)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f156,f7935])).
% 13.76/2.13  fof(f7935,plain,(
% 13.76/2.13    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK7(sK0,X1))) ) | ~spl8_4),
% 13.76/2.13    inference(superposition,[],[f112,f133])).
% 13.76/2.13  fof(f133,plain,(
% 13.76/2.13    sK0 = k3_tarski(sK0) | ~spl8_4),
% 13.76/2.13    inference(avatar_component_clause,[],[f132])).
% 13.76/2.13  fof(f112,plain,(
% 13.76/2.13    ( ! [X0,X5] : (~r2_hidden(X5,k3_tarski(X0)) | r2_hidden(X5,sK7(X0,X5))) )),
% 13.76/2.13    inference(equality_resolution,[],[f88])).
% 13.76/2.13  fof(f88,plain,(
% 13.76/2.13    ( ! [X0,X5,X1] : (r2_hidden(X5,sK7(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 13.76/2.13    inference(cnf_transformation,[],[f57])).
% 13.76/2.13  fof(f57,plain,(
% 13.76/2.13    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 13.76/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f53,f56,f55,f54])).
% 13.76/2.13  fof(f54,plain,(
% 13.76/2.13    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 13.76/2.13    introduced(choice_axiom,[])).
% 13.76/2.13  fof(f55,plain,(
% 13.76/2.13    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 13.76/2.13    introduced(choice_axiom,[])).
% 13.76/2.13  fof(f56,plain,(
% 13.76/2.13    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 13.76/2.13    introduced(choice_axiom,[])).
% 13.76/2.13  fof(f53,plain,(
% 13.76/2.13    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 13.76/2.13    inference(rectify,[],[f52])).
% 13.76/2.13  fof(f52,plain,(
% 13.76/2.13    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 13.76/2.13    inference(nnf_transformation,[],[f2])).
% 13.76/2.13  fof(f2,axiom,(
% 13.76/2.13    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 13.76/2.13  fof(f156,plain,(
% 13.76/2.13    r2_hidden(sK1,sK0) | ~spl8_5),
% 13.76/2.13    inference(avatar_component_clause,[],[f155])).
% 13.76/2.13  fof(f10653,plain,(
% 13.76/2.13    spl8_148 | ~spl8_4 | ~spl8_5),
% 13.76/2.13    inference(avatar_split_clause,[],[f8165,f155,f132,f10650])).
% 13.76/2.13  fof(f8165,plain,(
% 13.76/2.13    r2_hidden(sK7(sK0,sK1),sK0) | (~spl8_4 | ~spl8_5)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f156,f7934])).
% 13.76/2.13  fof(f7934,plain,(
% 13.76/2.13    ( ! [X0] : (r2_hidden(sK7(sK0,X0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 13.76/2.13    inference(superposition,[],[f111,f133])).
% 13.76/2.13  fof(f111,plain,(
% 13.76/2.13    ( ! [X0,X5] : (~r2_hidden(X5,k3_tarski(X0)) | r2_hidden(sK7(X0,X5),X0)) )),
% 13.76/2.13    inference(equality_resolution,[],[f89])).
% 13.76/2.13  fof(f89,plain,(
% 13.76/2.13    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 13.76/2.13    inference(cnf_transformation,[],[f57])).
% 13.76/2.13  fof(f7932,plain,(
% 13.76/2.13    spl8_4 | ~spl8_1 | ~spl8_11 | spl8_36 | spl8_59),
% 13.76/2.13    inference(avatar_split_clause,[],[f5463,f3130,f1963,f289,f115,f132])).
% 13.76/2.13  fof(f289,plain,(
% 13.76/2.13    spl8_11 <=> v3_ordinal1(k3_tarski(sK0))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 13.76/2.13  fof(f1963,plain,(
% 13.76/2.13    spl8_36 <=> r2_hidden(k3_tarski(sK0),sK4(sK0))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 13.76/2.13  fof(f3130,plain,(
% 13.76/2.13    spl8_59 <=> r2_hidden(sK7(sK0,sK0),sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 13.76/2.13  fof(f5463,plain,(
% 13.76/2.13    sK0 = k3_tarski(sK0) | (~spl8_1 | ~spl8_11 | spl8_36 | spl8_59)),
% 13.76/2.13    inference(subsumption_resolution,[],[f5462,f3131])).
% 13.76/2.13  fof(f3131,plain,(
% 13.76/2.13    ~r2_hidden(sK7(sK0,sK0),sK0) | spl8_59),
% 13.76/2.13    inference(avatar_component_clause,[],[f3130])).
% 13.76/2.13  fof(f5462,plain,(
% 13.76/2.13    sK0 = k3_tarski(sK0) | r2_hidden(sK7(sK0,sK0),sK0) | (~spl8_1 | ~spl8_11 | spl8_36)),
% 13.76/2.13    inference(subsumption_resolution,[],[f4868,f2706])).
% 13.76/2.13  fof(f2706,plain,(
% 13.76/2.13    ~r2_hidden(k3_tarski(sK0),sK0) | (~spl8_11 | spl8_36)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f291,f1965,f81])).
% 13.76/2.13  fof(f81,plain,(
% 13.76/2.13    ( ! [X2,X0] : (~v3_ordinal1(X2) | r2_hidden(X2,sK4(X0)) | ~r2_hidden(X2,X0)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f48])).
% 13.76/2.13  fof(f48,plain,(
% 13.76/2.13    ! [X0] : ! [X2] : ((r2_hidden(X2,sK4(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK4(X0))))),
% 13.76/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 13.76/2.13  fof(f47,plain,(
% 13.76/2.13    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK4(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK4(X0)))))),
% 13.76/2.13    introduced(choice_axiom,[])).
% 13.76/2.13  fof(f46,plain,(
% 13.76/2.13    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 13.76/2.13    inference(flattening,[],[f45])).
% 13.76/2.13  fof(f45,plain,(
% 13.76/2.13    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (~v3_ordinal1(X2) | ~r2_hidden(X2,X0))) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 13.76/2.13    inference(nnf_transformation,[],[f6])).
% 13.76/2.13  fof(f6,axiom,(
% 13.76/2.13    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).
% 13.76/2.13  fof(f1965,plain,(
% 13.76/2.13    ~r2_hidden(k3_tarski(sK0),sK4(sK0)) | spl8_36),
% 13.76/2.13    inference(avatar_component_clause,[],[f1963])).
% 13.76/2.13  fof(f291,plain,(
% 13.76/2.13    v3_ordinal1(k3_tarski(sK0)) | ~spl8_11),
% 13.76/2.13    inference(avatar_component_clause,[],[f289])).
% 13.76/2.13  fof(f4868,plain,(
% 13.76/2.13    sK0 = k3_tarski(sK0) | r2_hidden(k3_tarski(sK0),sK0) | r2_hidden(sK7(sK0,sK0),sK0) | (~spl8_1 | ~spl8_11)),
% 13.76/2.13    inference(resolution,[],[f481,f291])).
% 13.76/2.13  fof(f481,plain,(
% 13.76/2.13    ( ! [X4] : (~v3_ordinal1(k3_tarski(X4)) | sK0 = k3_tarski(X4) | r2_hidden(k3_tarski(X4),sK0) | r2_hidden(sK7(X4,sK0),X4)) ) | ~spl8_1),
% 13.76/2.13    inference(resolution,[],[f209,f111])).
% 13.76/2.13  fof(f6335,plain,(
% 13.76/2.13    ~spl8_89 | ~spl8_5),
% 13.76/2.13    inference(avatar_split_clause,[],[f6121,f155,f6332])).
% 13.76/2.13  fof(f6121,plain,(
% 13.76/2.13    ~r1_tarski(sK0,sK1) | ~spl8_5),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f156,f97])).
% 13.76/2.13  fof(f6088,plain,(
% 13.76/2.13    ~spl8_88 | ~spl8_2),
% 13.76/2.13    inference(avatar_split_clause,[],[f5997,f120,f6085])).
% 13.76/2.13  fof(f120,plain,(
% 13.76/2.13    spl8_2 <=> v4_ordinal1(sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 13.76/2.13  fof(f5997,plain,(
% 13.76/2.13    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~spl8_2),
% 13.76/2.13    inference(subsumption_resolution,[],[f98,f121])).
% 13.76/2.13  fof(f121,plain,(
% 13.76/2.13    v4_ordinal1(sK0) | ~spl8_2),
% 13.76/2.13    inference(avatar_component_clause,[],[f120])).
% 13.76/2.13  fof(f98,plain,(
% 13.76/2.13    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 13.76/2.13    inference(definition_unfolding,[],[f64,f67])).
% 13.76/2.13  fof(f64,plain,(
% 13.76/2.13    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 13.76/2.13    inference(cnf_transformation,[],[f38])).
% 13.76/2.13  fof(f38,plain,(
% 13.76/2.13    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 13.76/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 13.76/2.13  fof(f36,plain,(
% 13.76/2.13    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 13.76/2.13    introduced(choice_axiom,[])).
% 13.76/2.13  fof(f37,plain,(
% 13.76/2.13    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 13.76/2.13    introduced(choice_axiom,[])).
% 13.76/2.13  fof(f35,plain,(
% 13.76/2.13    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 13.76/2.13    inference(rectify,[],[f34])).
% 13.76/2.13  fof(f34,plain,(
% 13.76/2.13    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 13.76/2.13    inference(flattening,[],[f33])).
% 13.76/2.13  fof(f33,plain,(
% 13.76/2.13    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 13.76/2.13    inference(nnf_transformation,[],[f20])).
% 13.76/2.13  fof(f20,plain,(
% 13.76/2.13    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 13.76/2.13    inference(flattening,[],[f19])).
% 13.76/2.13  fof(f19,plain,(
% 13.76/2.13    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 13.76/2.13    inference(ennf_transformation,[],[f18])).
% 13.76/2.13  fof(f18,negated_conjecture,(
% 13.76/2.13    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 13.76/2.13    inference(negated_conjecture,[],[f17])).
% 13.76/2.13  fof(f17,conjecture,(
% 13.76/2.13    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 13.76/2.13  fof(f6083,plain,(
% 13.76/2.13    spl8_5 | ~spl8_2),
% 13.76/2.13    inference(avatar_split_clause,[],[f5996,f120,f155])).
% 13.76/2.13  fof(f5996,plain,(
% 13.76/2.13    r2_hidden(sK1,sK0) | ~spl8_2),
% 13.76/2.13    inference(subsumption_resolution,[],[f63,f121])).
% 13.76/2.13  fof(f63,plain,(
% 13.76/2.13    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 13.76/2.13    inference(cnf_transformation,[],[f38])).
% 13.76/2.13  fof(f5457,plain,(
% 13.76/2.13    ~spl8_2 | spl8_4),
% 13.76/2.13    inference(avatar_contradiction_clause,[],[f5456])).
% 13.76/2.13  fof(f5456,plain,(
% 13.76/2.13    $false | (~spl8_2 | spl8_4)),
% 13.76/2.13    inference(subsumption_resolution,[],[f121,f851])).
% 13.76/2.13  fof(f851,plain,(
% 13.76/2.13    ~v4_ordinal1(sK0) | spl8_4),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f134,f74])).
% 13.76/2.13  fof(f74,plain,(
% 13.76/2.13    ( ! [X0] : (~v4_ordinal1(X0) | k3_tarski(X0) = X0) )),
% 13.76/2.13    inference(cnf_transformation,[],[f42])).
% 13.76/2.13  fof(f42,plain,(
% 13.76/2.13    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 13.76/2.13    inference(nnf_transformation,[],[f4])).
% 13.76/2.13  fof(f4,axiom,(
% 13.76/2.13    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).
% 13.76/2.13  fof(f134,plain,(
% 13.76/2.13    sK0 != k3_tarski(sK0) | spl8_4),
% 13.76/2.13    inference(avatar_component_clause,[],[f132])).
% 13.76/2.13  fof(f5441,plain,(
% 13.76/2.13    ~spl8_1 | ~spl8_73 | spl8_80 | ~spl8_83),
% 13.76/2.13    inference(avatar_contradiction_clause,[],[f5440])).
% 13.76/2.13  fof(f5440,plain,(
% 13.76/2.13    $false | (~spl8_1 | ~spl8_73 | spl8_80 | ~spl8_83)),
% 13.76/2.13    inference(subsumption_resolution,[],[f5436,f5001])).
% 13.76/2.13  fof(f5001,plain,(
% 13.76/2.13    r1_ordinal1(sK7(sK0,sK0),sK0) | ~spl8_83),
% 13.76/2.13    inference(avatar_component_clause,[],[f4999])).
% 13.76/2.13  fof(f4999,plain,(
% 13.76/2.13    spl8_83 <=> r1_ordinal1(sK7(sK0,sK0),sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 13.76/2.13  fof(f5436,plain,(
% 13.76/2.13    ~r1_ordinal1(sK7(sK0,sK0),sK0) | (~spl8_1 | ~spl8_73 | spl8_80)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f3885,f4864,f186])).
% 13.76/2.13  fof(f186,plain,(
% 13.76/2.13    ( ! [X0] : (~r1_ordinal1(X0,sK0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) ) | ~spl8_1),
% 13.76/2.13    inference(resolution,[],[f83,f117])).
% 13.76/2.13  fof(f4864,plain,(
% 13.76/2.13    ~r1_tarski(sK7(sK0,sK0),sK0) | spl8_80),
% 13.76/2.13    inference(avatar_component_clause,[],[f4862])).
% 13.76/2.13  fof(f4862,plain,(
% 13.76/2.13    spl8_80 <=> r1_tarski(sK7(sK0,sK0),sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 13.76/2.13  fof(f3885,plain,(
% 13.76/2.13    v3_ordinal1(sK7(sK0,sK0)) | ~spl8_73),
% 13.76/2.13    inference(avatar_component_clause,[],[f3883])).
% 13.76/2.13  fof(f3883,plain,(
% 13.76/2.13    spl8_73 <=> v3_ordinal1(sK7(sK0,sK0))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).
% 13.76/2.13  fof(f5002,plain,(
% 13.76/2.13    spl8_83 | ~spl8_1 | ~spl8_59),
% 13.76/2.13    inference(avatar_split_clause,[],[f3777,f3130,f115,f4999])).
% 13.76/2.13  fof(f3777,plain,(
% 13.76/2.13    r1_ordinal1(sK7(sK0,sK0),sK0) | (~spl8_1 | ~spl8_59)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f3132,f526])).
% 13.76/2.13  fof(f526,plain,(
% 13.76/2.13    ( ! [X1] : (r1_ordinal1(X1,sK0) | ~r2_hidden(X1,sK0)) ) | ~spl8_1),
% 13.76/2.13    inference(subsumption_resolution,[],[f520,f149])).
% 13.76/2.13  fof(f520,plain,(
% 13.76/2.13    ( ! [X1] : (r1_ordinal1(X1,sK0) | ~v3_ordinal1(X1) | ~r2_hidden(X1,sK0)) ) | ~spl8_1),
% 13.76/2.13    inference(resolution,[],[f219,f106])).
% 13.76/2.13  fof(f106,plain,(
% 13.76/2.13    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 13.76/2.13    inference(definition_unfolding,[],[f95,f67])).
% 13.76/2.13  fof(f95,plain,(
% 13.76/2.13    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 13.76/2.13    inference(cnf_transformation,[],[f59])).
% 13.76/2.13  fof(f59,plain,(
% 13.76/2.13    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 13.76/2.13    inference(flattening,[],[f58])).
% 13.76/2.13  fof(f58,plain,(
% 13.76/2.13    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 13.76/2.13    inference(nnf_transformation,[],[f8])).
% 13.76/2.13  fof(f8,axiom,(
% 13.76/2.13    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 13.76/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 13.76/2.13  fof(f219,plain,(
% 13.76/2.13    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK0,k1_tarski(sK0))) | r1_ordinal1(X0,sK0) | ~v3_ordinal1(X0)) ) | ~spl8_1),
% 13.76/2.13    inference(resolution,[],[f104,f117])).
% 13.76/2.13  fof(f3132,plain,(
% 13.76/2.13    r2_hidden(sK7(sK0,sK0),sK0) | ~spl8_59),
% 13.76/2.13    inference(avatar_component_clause,[],[f3130])).
% 13.76/2.13  fof(f4865,plain,(
% 13.76/2.13    ~spl8_80 | ~spl8_58),
% 13.76/2.13    inference(avatar_split_clause,[],[f3626,f2962,f4862])).
% 13.76/2.13  fof(f2962,plain,(
% 13.76/2.13    spl8_58 <=> r2_hidden(sK0,sK7(sK0,sK0))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 13.76/2.13  fof(f3626,plain,(
% 13.76/2.13    ~r1_tarski(sK7(sK0,sK0),sK0) | ~spl8_58),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f2964,f97])).
% 13.76/2.13  fof(f2964,plain,(
% 13.76/2.13    r2_hidden(sK0,sK7(sK0,sK0)) | ~spl8_58),
% 13.76/2.13    inference(avatar_component_clause,[],[f2962])).
% 13.76/2.13  fof(f3886,plain,(
% 13.76/2.13    spl8_73 | ~spl8_1 | ~spl8_59),
% 13.76/2.13    inference(avatar_split_clause,[],[f3778,f3130,f115,f3883])).
% 13.76/2.13  fof(f3778,plain,(
% 13.76/2.13    v3_ordinal1(sK7(sK0,sK0)) | (~spl8_1 | ~spl8_59)),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f117,f3132,f82])).
% 13.76/2.13  fof(f2965,plain,(
% 13.76/2.13    spl8_58 | ~spl8_17),
% 13.76/2.13    inference(avatar_split_clause,[],[f1153,f728,f2962])).
% 13.76/2.13  fof(f728,plain,(
% 13.76/2.13    spl8_17 <=> r2_hidden(sK0,k3_tarski(sK0))),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 13.76/2.13  fof(f1153,plain,(
% 13.76/2.13    r2_hidden(sK0,sK7(sK0,sK0)) | ~spl8_17),
% 13.76/2.13    inference(unit_resulting_resolution,[],[f730,f112])).
% 13.76/2.13  fof(f730,plain,(
% 13.76/2.13    r2_hidden(sK0,k3_tarski(sK0)) | ~spl8_17),
% 13.76/2.13    inference(avatar_component_clause,[],[f728])).
% 13.76/2.13  fof(f1966,plain,(
% 13.76/2.13    ~spl8_36 | spl8_16),
% 13.76/2.13    inference(avatar_split_clause,[],[f619,f558,f1963])).
% 13.76/2.13  fof(f558,plain,(
% 13.76/2.13    spl8_16 <=> r2_hidden(k3_tarski(sK0),sK0)),
% 13.76/2.13    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 13.76/2.15  fof(f619,plain,(
% 13.76/2.15    ~r2_hidden(k3_tarski(sK0),sK4(sK0)) | spl8_16),
% 13.76/2.15    inference(unit_resulting_resolution,[],[f560,f79])).
% 13.76/2.15  fof(f79,plain,(
% 13.76/2.15    ( ! [X2,X0] : (~r2_hidden(X2,sK4(X0)) | r2_hidden(X2,X0)) )),
% 13.76/2.15    inference(cnf_transformation,[],[f48])).
% 13.76/2.15  fof(f560,plain,(
% 13.76/2.15    ~r2_hidden(k3_tarski(sK0),sK0) | spl8_16),
% 13.76/2.15    inference(avatar_component_clause,[],[f558])).
% 13.76/2.15  fof(f835,plain,(
% 13.76/2.15    ~spl8_3 | spl8_9),
% 13.76/2.15    inference(avatar_split_clause,[],[f287,f266,f124])).
% 13.76/2.15  fof(f287,plain,(
% 13.76/2.15    ~v3_ordinal1(sK1) | spl8_9),
% 13.76/2.15    inference(resolution,[],[f268,f102])).
% 13.76/2.15  fof(f102,plain,(
% 13.76/2.15    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 13.76/2.15    inference(definition_unfolding,[],[f68,f67])).
% 13.76/2.15  fof(f68,plain,(
% 13.76/2.15    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 13.76/2.15    inference(cnf_transformation,[],[f21])).
% 13.76/2.15  fof(f21,plain,(
% 13.76/2.15    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 13.76/2.15    inference(ennf_transformation,[],[f12])).
% 13.76/2.15  fof(f12,axiom,(
% 13.76/2.15    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 13.76/2.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 13.76/2.15  fof(f268,plain,(
% 13.76/2.15    ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | spl8_9),
% 13.76/2.15    inference(avatar_component_clause,[],[f266])).
% 13.76/2.15  fof(f731,plain,(
% 13.76/2.15    spl8_17 | ~spl8_1 | spl8_4 | ~spl8_11 | spl8_16),
% 13.76/2.15    inference(avatar_split_clause,[],[f616,f558,f289,f132,f115,f728])).
% 13.76/2.15  fof(f616,plain,(
% 13.76/2.15    r2_hidden(sK0,k3_tarski(sK0)) | (~spl8_1 | spl8_4 | ~spl8_11 | spl8_16)),
% 13.76/2.15    inference(unit_resulting_resolution,[],[f117,f291,f134,f560,f71])).
% 13.76/2.15  fof(f561,plain,(
% 13.76/2.15    ~spl8_16 | ~spl8_1 | ~spl8_6),
% 13.76/2.15    inference(avatar_split_clause,[],[f550,f160,f115,f558])).
% 13.76/2.15  fof(f160,plain,(
% 13.76/2.15    spl8_6 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 13.76/2.15    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 13.76/2.15  fof(f550,plain,(
% 13.76/2.15    ~r2_hidden(k3_tarski(sK0),sK0) | (~spl8_1 | ~spl8_6)),
% 13.76/2.15    inference(unit_resulting_resolution,[],[f137,f101,f200])).
% 13.76/2.15  fof(f200,plain,(
% 13.76/2.15    ( ! [X8,X7] : (~r2_hidden(X8,sK0) | ~r2_hidden(X7,k2_xboole_0(X8,k1_tarski(X8))) | r2_hidden(X7,k3_tarski(sK0))) ) | (~spl8_1 | ~spl8_6)),
% 13.76/2.15    inference(resolution,[],[f110,f163])).
% 13.76/2.15  fof(f163,plain,(
% 13.76/2.15    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | (~spl8_1 | ~spl8_6)),
% 13.76/2.15    inference(subsumption_resolution,[],[f161,f149])).
% 13.76/2.15  fof(f161,plain,(
% 13.76/2.15    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0)) ) | ~spl8_6),
% 13.76/2.15    inference(avatar_component_clause,[],[f160])).
% 13.76/2.15  fof(f110,plain,(
% 13.76/2.15    ( ! [X6,X0,X5] : (~r2_hidden(X6,X0) | r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X5,X6)) )),
% 13.76/2.15    inference(equality_resolution,[],[f90])).
% 13.76/2.15  fof(f90,plain,(
% 13.76/2.15    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 13.76/2.15    inference(cnf_transformation,[],[f57])).
% 13.76/2.15  fof(f101,plain,(
% 13.76/2.15    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 13.76/2.15    inference(definition_unfolding,[],[f66,f67])).
% 13.76/2.15  fof(f66,plain,(
% 13.76/2.15    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 13.76/2.15    inference(cnf_transformation,[],[f7])).
% 13.76/2.15  fof(f7,axiom,(
% 13.76/2.15    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 13.76/2.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 13.76/2.15  fof(f137,plain,(
% 13.76/2.15    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 13.76/2.15    inference(unit_resulting_resolution,[],[f108,f97])).
% 13.76/2.15  fof(f108,plain,(
% 13.76/2.15    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 13.76/2.15    inference(equality_resolution,[],[f86])).
% 13.76/2.15  fof(f86,plain,(
% 13.76/2.15    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 13.76/2.15    inference(cnf_transformation,[],[f51])).
% 13.76/2.15  fof(f51,plain,(
% 13.76/2.15    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.76/2.15    inference(flattening,[],[f50])).
% 13.76/2.15  fof(f50,plain,(
% 13.76/2.15    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.76/2.15    inference(nnf_transformation,[],[f1])).
% 13.76/2.15  fof(f1,axiom,(
% 13.76/2.15    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 13.76/2.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 13.76/2.15  fof(f292,plain,(
% 13.76/2.15    spl8_11 | ~spl8_1),
% 13.76/2.15    inference(avatar_split_clause,[],[f275,f115,f289])).
% 13.76/2.15  fof(f275,plain,(
% 13.76/2.15    v3_ordinal1(k3_tarski(sK0)) | ~spl8_1),
% 13.76/2.15    inference(subsumption_resolution,[],[f272,f73])).
% 13.76/2.15  fof(f73,plain,(
% 13.76/2.15    ( ! [X0] : (~v3_ordinal1(sK2(X0)) | v3_ordinal1(k3_tarski(X0))) )),
% 13.76/2.15    inference(cnf_transformation,[],[f41])).
% 13.76/2.15  fof(f41,plain,(
% 13.76/2.15    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 13.76/2.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f40])).
% 13.76/2.15  fof(f40,plain,(
% 13.76/2.15    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 13.76/2.15    introduced(choice_axiom,[])).
% 13.76/2.15  fof(f25,plain,(
% 13.76/2.15    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 13.76/2.15    inference(ennf_transformation,[],[f14])).
% 13.76/2.15  fof(f14,axiom,(
% 13.76/2.15    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 13.76/2.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).
% 13.76/2.15  fof(f272,plain,(
% 13.76/2.15    v3_ordinal1(sK2(sK0)) | v3_ordinal1(k3_tarski(sK0)) | ~spl8_1),
% 13.76/2.15    inference(resolution,[],[f149,f72])).
% 13.76/2.15  fof(f72,plain,(
% 13.76/2.15    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v3_ordinal1(k3_tarski(X0))) )),
% 13.76/2.15    inference(cnf_transformation,[],[f41])).
% 13.76/2.15  fof(f162,plain,(
% 13.76/2.15    spl8_2 | spl8_6),
% 13.76/2.15    inference(avatar_split_clause,[],[f99,f160,f120])).
% 13.76/2.15  fof(f99,plain,(
% 13.76/2.15    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 13.76/2.15    inference(definition_unfolding,[],[f61,f67])).
% 13.76/2.15  fof(f61,plain,(
% 13.76/2.15    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 13.76/2.15    inference(cnf_transformation,[],[f38])).
% 13.76/2.15  fof(f135,plain,(
% 13.76/2.15    ~spl8_4 | spl8_2),
% 13.76/2.15    inference(avatar_split_clause,[],[f128,f120,f132])).
% 13.76/2.15  fof(f128,plain,(
% 13.76/2.15    sK0 != k3_tarski(sK0) | spl8_2),
% 13.76/2.15    inference(unit_resulting_resolution,[],[f122,f75])).
% 13.76/2.15  fof(f75,plain,(
% 13.76/2.15    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 13.76/2.15    inference(cnf_transformation,[],[f42])).
% 13.76/2.15  fof(f122,plain,(
% 13.76/2.15    ~v4_ordinal1(sK0) | spl8_2),
% 13.76/2.15    inference(avatar_component_clause,[],[f120])).
% 13.76/2.15  fof(f127,plain,(
% 13.76/2.15    ~spl8_2 | spl8_3),
% 13.76/2.15    inference(avatar_split_clause,[],[f62,f124,f120])).
% 13.76/2.15  fof(f62,plain,(
% 13.76/2.15    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 13.76/2.15    inference(cnf_transformation,[],[f38])).
% 13.76/2.15  fof(f118,plain,(
% 13.76/2.15    spl8_1),
% 13.76/2.15    inference(avatar_split_clause,[],[f60,f115])).
% 13.76/2.15  fof(f60,plain,(
% 13.76/2.15    v3_ordinal1(sK0)),
% 13.76/2.15    inference(cnf_transformation,[],[f38])).
% 13.76/2.15  % SZS output end Proof for theBenchmark
% 13.76/2.15  % (21363)------------------------------
% 13.76/2.15  % (21363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.76/2.15  % (21363)Termination reason: Refutation
% 13.76/2.15  
% 13.76/2.15  % (21363)Memory used [KB]: 26097
% 13.76/2.15  % (21363)Time elapsed: 1.689 s
% 13.76/2.15  % (21363)------------------------------
% 13.76/2.15  % (21363)------------------------------
% 13.76/2.15  % (21342)Success in time 1.787 s
%------------------------------------------------------------------------------
