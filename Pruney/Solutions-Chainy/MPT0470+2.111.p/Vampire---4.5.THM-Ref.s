%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 142 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  246 ( 459 expanded)
%              Number of equality atoms :   36 (  78 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f69,f72,f155,f168,f182,f190,f198,f222])).

fof(f222,plain,
    ( spl8_2
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl8_2
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f68,f23,f68,f59,f161,f161,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK6(X0,X1,X2)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f161,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),k1_xboole_0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_9
  <=> ! [X3,X2] : ~ r2_hidden(k4_tarski(X2,X3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f59,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_2
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f68,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f198,plain,
    ( ~ spl8_6
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f197,f53,f160,f144,f66,f148])).

fof(f148,plain,
    ( spl8_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f144,plain,
    ( spl8_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f53,plain,
    ( spl8_1
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f124,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X1,X1) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X1,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X1,X0,X2,X3),X3),X4)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X4,X0) ) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f190,plain,
    ( ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl8_4
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f23,f68,f154,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f154,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_7
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f182,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl8_6 ),
    inference(subsumption_resolution,[],[f85,f150])).

fof(f150,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f85,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X2
      | r1_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f168,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f23,f146])).

fof(f146,plain,
    ( ~ v1_relat_1(sK0)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f155,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_4
    | ~ spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f142,f53,f152,f66,f148,f144])).

fof(f142,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl8_1 ),
    inference(superposition,[],[f55,f133])).

fof(f133,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 = k5_relat_1(X5,X6)
      | ~ v1_relat_1(k5_relat_1(X5,X6))
      | ~ v1_relat_1(X6)
      | ~ r1_xboole_0(X6,X6)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X5,X6))
      | ~ v1_relat_1(X6)
      | ~ r1_xboole_0(X6,X6)
      | ~ v1_relat_1(k5_relat_1(X5,X6))
      | k1_xboole_0 = k5_relat_1(X5,X6) ) ),
    inference(resolution,[],[f124,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f55,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f72,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f23,f64])).

fof(f64,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_3
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f69,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f61,f66,f63])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f60,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f22,f57,f53])).

fof(f22,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 13:02:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.45  % (29181)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (29190)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (29176)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (29199)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (29176)Refutation not found, incomplete strategy% (29176)------------------------------
% 0.19/0.52  % (29176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (29176)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (29176)Memory used [KB]: 1663
% 0.19/0.52  % (29176)Time elapsed: 0.121 s
% 0.19/0.52  % (29176)------------------------------
% 0.19/0.52  % (29176)------------------------------
% 0.19/0.52  % (29191)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (29195)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.53  % (29194)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (29185)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.53  % (29183)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.53  % (29193)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.53  % (29201)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (29201)Refutation not found, incomplete strategy% (29201)------------------------------
% 0.19/0.53  % (29201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (29201)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (29201)Memory used [KB]: 10618
% 0.19/0.53  % (29201)Time elapsed: 0.126 s
% 0.19/0.53  % (29201)------------------------------
% 0.19/0.53  % (29201)------------------------------
% 0.19/0.53  % (29182)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (29200)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.54  % (29186)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.54  % (29188)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.54  % (29186)Refutation not found, incomplete strategy% (29186)------------------------------
% 0.19/0.54  % (29186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (29186)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (29186)Memory used [KB]: 10746
% 0.19/0.54  % (29186)Time elapsed: 0.147 s
% 0.19/0.54  % (29186)------------------------------
% 0.19/0.54  % (29186)------------------------------
% 0.19/0.54  % (29180)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.54  % (29179)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.54  % (29178)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.54  % (29196)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.55  % (29206)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.55  % (29206)Refutation not found, incomplete strategy% (29206)------------------------------
% 0.19/0.55  % (29206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (29206)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (29206)Memory used [KB]: 1663
% 0.19/0.55  % (29206)Time elapsed: 0.001 s
% 0.19/0.55  % (29206)------------------------------
% 0.19/0.55  % (29206)------------------------------
% 0.19/0.55  % (29197)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.55  % (29203)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (29202)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.55  % (29189)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.55  % (29204)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.55  % (29187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.55  % (29189)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.55  % (29204)Refutation not found, incomplete strategy% (29204)------------------------------
% 0.19/0.55  % (29204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (29192)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.56  % (29205)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.56  % (29204)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (29204)Memory used [KB]: 6140
% 0.19/0.56  % (29204)Time elapsed: 0.162 s
% 0.19/0.56  % (29204)------------------------------
% 0.19/0.56  % (29204)------------------------------
% 0.19/0.56  % (29184)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.57  % (29205)Refutation not found, incomplete strategy% (29205)------------------------------
% 0.19/0.57  % (29205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (29205)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (29205)Memory used [KB]: 10746
% 0.19/0.57  % (29205)Time elapsed: 0.170 s
% 0.19/0.57  % (29205)------------------------------
% 0.19/0.57  % (29205)------------------------------
% 0.19/0.57  % (29192)Refutation not found, incomplete strategy% (29192)------------------------------
% 0.19/0.57  % (29192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (29192)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  % (29175)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.57  
% 0.19/0.57  % (29192)Memory used [KB]: 10618
% 0.19/0.57  % (29192)Time elapsed: 0.165 s
% 0.19/0.57  % (29192)------------------------------
% 0.19/0.57  % (29192)------------------------------
% 0.19/0.57  % SZS output start Proof for theBenchmark
% 0.19/0.57  fof(f223,plain,(
% 0.19/0.57    $false),
% 0.19/0.57    inference(avatar_sat_refutation,[],[f60,f69,f72,f155,f168,f182,f190,f198,f222])).
% 0.19/0.57  fof(f222,plain,(
% 0.19/0.57    spl8_2 | ~spl8_4 | ~spl8_9),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f215])).
% 0.19/0.57  fof(f215,plain,(
% 0.19/0.57    $false | (spl8_2 | ~spl8_4 | ~spl8_9)),
% 0.19/0.57    inference(unit_resulting_resolution,[],[f68,f23,f68,f59,f161,f161,f27])).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK6(X0,X1,X2)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 0.19/0.57    inference(cnf_transformation,[],[f17])).
% 0.19/0.57  fof(f17,plain,(
% 0.19/0.57    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f7])).
% 0.19/0.57  fof(f7,axiom,(
% 0.19/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.19/0.57  fof(f161,plain,(
% 0.19/0.57    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k1_xboole_0)) ) | ~spl8_9),
% 0.19/0.57    inference(avatar_component_clause,[],[f160])).
% 0.19/0.57  fof(f160,plain,(
% 0.19/0.57    spl8_9 <=> ! [X3,X2] : ~r2_hidden(k4_tarski(X2,X3),k1_xboole_0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.19/0.57  fof(f59,plain,(
% 0.19/0.57    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl8_2),
% 0.19/0.57    inference(avatar_component_clause,[],[f57])).
% 0.19/0.57  fof(f57,plain,(
% 0.19/0.57    spl8_2 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.19/0.57  fof(f23,plain,(
% 0.19/0.57    v1_relat_1(sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f14])).
% 0.19/0.57  fof(f14,plain,(
% 0.19/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f12])).
% 0.19/0.57  fof(f12,negated_conjecture,(
% 0.19/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.57    inference(negated_conjecture,[],[f11])).
% 0.19/0.57  fof(f11,conjecture,(
% 0.19/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.19/0.57  fof(f68,plain,(
% 0.19/0.57    v1_relat_1(k1_xboole_0) | ~spl8_4),
% 0.19/0.57    inference(avatar_component_clause,[],[f66])).
% 0.19/0.57  fof(f66,plain,(
% 0.19/0.57    spl8_4 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.19/0.57  fof(f198,plain,(
% 0.19/0.57    ~spl8_6 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_1),
% 0.19/0.57    inference(avatar_split_clause,[],[f197,f53,f160,f144,f66,f148])).
% 0.19/0.57  fof(f148,plain,(
% 0.19/0.57    spl8_6 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.19/0.57  fof(f144,plain,(
% 0.19/0.57    spl8_5 <=> v1_relat_1(sK0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.19/0.57  fof(f53,plain,(
% 0.19/0.57    spl8_1 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.19/0.57  fof(f197,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl8_1),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f193])).
% 0.19/0.57  fof(f193,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl8_1),
% 0.19/0.57    inference(superposition,[],[f124,f54])).
% 0.19/0.57  fof(f54,plain,(
% 0.19/0.57    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl8_1),
% 0.19/0.57    inference(avatar_component_clause,[],[f53])).
% 0.19/0.57  fof(f124,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~r1_xboole_0(X1,X1)) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f122])).
% 0.19/0.57  fof(f122,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~r1_xboole_0(X1,X1) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1))) )),
% 0.19/0.57    inference(resolution,[],[f103,f48])).
% 0.19/0.57  fof(f48,plain,(
% 0.19/0.57    ( ! [X4,X0,X3,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.19/0.57    inference(equality_resolution,[],[f30])).
% 0.19/0.57  fof(f30,plain,(
% 0.19/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.19/0.57    inference(cnf_transformation,[],[f17])).
% 0.19/0.57  fof(f103,plain,(
% 0.19/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK5(X1,X0,X2,X3),X3),X4) | ~v1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~r1_xboole_0(X4,X0)) )),
% 0.19/0.57    inference(resolution,[],[f48,f33])).
% 0.19/0.57  fof(f33,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f18])).
% 0.19/0.57  fof(f18,plain,(
% 0.19/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f13])).
% 0.19/0.57  fof(f13,plain,(
% 0.19/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.57    inference(rectify,[],[f1])).
% 0.19/0.57  fof(f1,axiom,(
% 0.19/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.57  fof(f190,plain,(
% 0.19/0.57    ~spl8_4 | spl8_7),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f186])).
% 0.19/0.57  fof(f186,plain,(
% 0.19/0.57    $false | (~spl8_4 | spl8_7)),
% 0.19/0.57    inference(unit_resulting_resolution,[],[f23,f68,f154,f37])).
% 0.19/0.57  fof(f37,plain,(
% 0.19/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f21])).
% 0.19/0.57  fof(f21,plain,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.19/0.57    inference(flattening,[],[f20])).
% 0.19/0.57  fof(f20,plain,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.19/0.57    inference(ennf_transformation,[],[f8])).
% 0.19/0.57  fof(f8,axiom,(
% 0.19/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.19/0.57  fof(f154,plain,(
% 0.19/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl8_7),
% 0.19/0.57    inference(avatar_component_clause,[],[f152])).
% 0.19/0.57  fof(f152,plain,(
% 0.19/0.57    spl8_7 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.19/0.57  fof(f182,plain,(
% 0.19/0.57    spl8_6),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f169])).
% 0.19/0.57  fof(f169,plain,(
% 0.19/0.57    $false | spl8_6),
% 0.19/0.57    inference(subsumption_resolution,[],[f85,f150])).
% 0.19/0.57  fof(f150,plain,(
% 0.19/0.57    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_6),
% 0.19/0.57    inference(avatar_component_clause,[],[f148])).
% 0.19/0.57  fof(f85,plain,(
% 0.19/0.57    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.57    inference(resolution,[],[f84,f50])).
% 0.19/0.57  fof(f50,plain,(
% 0.19/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.57    inference(equality_resolution,[],[f39])).
% 0.19/0.57  fof(f39,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f2,axiom,(
% 0.19/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.57  fof(f84,plain,(
% 0.19/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.57    inference(equality_resolution,[],[f77])).
% 0.19/0.57  fof(f77,plain,(
% 0.19/0.57    ( ! [X2,X3] : (k1_xboole_0 != X2 | r1_xboole_0(X2,X3) | ~r1_tarski(X2,X3)) )),
% 0.19/0.57    inference(superposition,[],[f41,f43])).
% 0.19/0.57  fof(f43,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f3])).
% 0.19/0.57  fof(f3,axiom,(
% 0.19/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.57  fof(f41,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f5])).
% 0.19/0.57  fof(f5,axiom,(
% 0.19/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.57  fof(f168,plain,(
% 0.19/0.57    spl8_5),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f167])).
% 0.19/0.57  fof(f167,plain,(
% 0.19/0.57    $false | spl8_5),
% 0.19/0.57    inference(subsumption_resolution,[],[f23,f146])).
% 0.19/0.57  fof(f146,plain,(
% 0.19/0.57    ~v1_relat_1(sK0) | spl8_5),
% 0.19/0.57    inference(avatar_component_clause,[],[f144])).
% 0.19/0.57  fof(f155,plain,(
% 0.19/0.57    ~spl8_5 | ~spl8_6 | ~spl8_4 | ~spl8_7 | spl8_1),
% 0.19/0.57    inference(avatar_split_clause,[],[f142,f53,f152,f66,f148,f144])).
% 0.19/0.57  fof(f142,plain,(
% 0.19/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(sK0) | spl8_1),
% 0.19/0.57    inference(trivial_inequality_removal,[],[f135])).
% 0.19/0.57  fof(f135,plain,(
% 0.19/0.57    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(sK0) | spl8_1),
% 0.19/0.57    inference(superposition,[],[f55,f133])).
% 0.19/0.57  fof(f133,plain,(
% 0.19/0.57    ( ! [X6,X5] : (k1_xboole_0 = k5_relat_1(X5,X6) | ~v1_relat_1(k5_relat_1(X5,X6)) | ~v1_relat_1(X6) | ~r1_xboole_0(X6,X6) | ~v1_relat_1(X5)) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f126])).
% 0.19/0.57  fof(f126,plain,(
% 0.19/0.57    ( ! [X6,X5] : (~v1_relat_1(X5) | ~v1_relat_1(k5_relat_1(X5,X6)) | ~v1_relat_1(X6) | ~r1_xboole_0(X6,X6) | ~v1_relat_1(k5_relat_1(X5,X6)) | k1_xboole_0 = k5_relat_1(X5,X6)) )),
% 0.19/0.57    inference(resolution,[],[f124,f25])).
% 0.19/0.57  fof(f25,plain,(
% 0.19/0.57    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.19/0.57    inference(cnf_transformation,[],[f16])).
% 0.19/0.57  fof(f16,plain,(
% 0.19/0.57    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.19/0.57    inference(flattening,[],[f15])).
% 0.19/0.57  fof(f15,plain,(
% 0.19/0.57    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f10])).
% 0.19/0.57  fof(f10,axiom,(
% 0.19/0.57    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.19/0.57  fof(f55,plain,(
% 0.19/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl8_1),
% 0.19/0.57    inference(avatar_component_clause,[],[f53])).
% 0.19/0.57  fof(f72,plain,(
% 0.19/0.57    ~spl8_3),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f70])).
% 0.19/0.57  fof(f70,plain,(
% 0.19/0.57    $false | ~spl8_3),
% 0.19/0.57    inference(subsumption_resolution,[],[f23,f64])).
% 0.19/0.57  fof(f64,plain,(
% 0.19/0.57    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl8_3),
% 0.19/0.57    inference(avatar_component_clause,[],[f63])).
% 0.19/0.57  fof(f63,plain,(
% 0.19/0.57    spl8_3 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.19/0.57  fof(f69,plain,(
% 0.19/0.57    spl8_3 | spl8_4),
% 0.19/0.57    inference(avatar_split_clause,[],[f61,f66,f63])).
% 0.19/0.57  fof(f61,plain,(
% 0.19/0.57    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.57    inference(superposition,[],[f46,f45])).
% 0.19/0.57  fof(f45,plain,(
% 0.19/0.57    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.19/0.57    inference(definition_unfolding,[],[f24,f32])).
% 0.19/0.57  fof(f32,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f6])).
% 0.19/0.57  fof(f6,axiom,(
% 0.19/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.57  fof(f24,plain,(
% 0.19/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f4])).
% 0.19/0.57  fof(f4,axiom,(
% 0.19/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.57  fof(f46,plain,(
% 0.19/0.57    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.19/0.57    inference(definition_unfolding,[],[f36,f32])).
% 0.19/0.57  fof(f36,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f19])).
% 0.19/0.57  fof(f19,plain,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f9])).
% 0.19/0.57  fof(f9,axiom,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.19/0.57  fof(f60,plain,(
% 0.19/0.57    ~spl8_1 | ~spl8_2),
% 0.19/0.57    inference(avatar_split_clause,[],[f22,f57,f53])).
% 0.19/0.57  fof(f22,plain,(
% 0.19/0.57    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.19/0.57    inference(cnf_transformation,[],[f14])).
% 0.19/0.57  % SZS output end Proof for theBenchmark
% 0.19/0.57  % (29189)------------------------------
% 0.19/0.57  % (29189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (29189)Termination reason: Refutation
% 0.19/0.57  
% 0.19/0.57  % (29189)Memory used [KB]: 6396
% 0.19/0.57  % (29189)Time elapsed: 0.173 s
% 0.19/0.57  % (29189)------------------------------
% 0.19/0.57  % (29189)------------------------------
% 0.19/0.57  % (29169)Success in time 0.226 s
%------------------------------------------------------------------------------
