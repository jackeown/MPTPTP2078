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
% DateTime   : Thu Dec  3 12:48:15 EST 2020

% Result     : Theorem 12.66s
% Output     : Refutation 12.66s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 171 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 500 expanded)
%              Number of equality atoms :   21 (  73 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3648,f3736,f6059,f7331,f7361,f7424])).

fof(f7424,plain,
    ( ~ spl12_10
    | ~ spl12_14 ),
    inference(avatar_contradiction_clause,[],[f7423])).

fof(f7423,plain,
    ( $false
    | ~ spl12_10
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f7422,f3655])).

fof(f3655,plain,
    ( r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ spl12_10 ),
    inference(resolution,[],[f3643,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f20,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f20,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f3643,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f3641])).

fof(f3641,plain,
    ( spl12_10
  <=> r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f7422,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ spl12_10
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f7421,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f7421,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ spl12_10
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f7404,f3643])).

fof(f7404,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0)
    | ~ spl12_14 ),
    inference(resolution,[],[f6058,f48])).

fof(f48,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f6058,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1) )
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f6057])).

fof(f6057,plain,
    ( spl12_14
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f7361,plain,
    ( spl12_10
    | ~ spl12_11
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(avatar_contradiction_clause,[],[f7332])).

fof(f7332,plain,
    ( $false
    | spl12_10
    | ~ spl12_11
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(unit_resulting_resolution,[],[f3647,f3642,f3735,f7315,f260])).

fof(f260,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X6),k6_relat_1(X5))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),sK1))
      | r2_hidden(k4_tarski(X3,X4),sK1)
      | ~ r2_hidden(k4_tarski(X6,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f259,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f259,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(k4_tarski(X3,X4),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),sK1))
      | ~ r2_hidden(k4_tarski(X3,X6),k6_relat_1(X5))
      | ~ r2_hidden(k4_tarski(X6,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f244,f22])).

fof(f244,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(k4_tarski(X3,X4),sK1)
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),sK1))
      | ~ r2_hidden(k4_tarski(X3,X6),k6_relat_1(X5))
      | ~ r2_hidden(k4_tarski(X6,X4),sK1) ) ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f70,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k5_relat_1(k6_relat_1(X7),sK1))
      | r2_hidden(k4_tarski(X5,X6),sK1) ) ),
    inference(resolution,[],[f19,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(f7315,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f7314])).

fof(f7314,plain,
    ( spl12_15
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f3735,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f3733])).

fof(f3733,plain,
    ( spl12_12
  <=> r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f3642,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | spl12_10 ),
    inference(avatar_component_clause,[],[f3641])).

fof(f3647,plain,
    ( r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f3645])).

fof(f3645,plain,
    ( spl12_11
  <=> r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f7331,plain,(
    spl12_15 ),
    inference(avatar_contradiction_clause,[],[f7330])).

fof(f7330,plain,
    ( $false
    | spl12_15 ),
    inference(subsumption_resolution,[],[f7329,f19])).

fof(f7329,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_15 ),
    inference(subsumption_resolution,[],[f7324,f22])).

fof(f7324,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl12_15 ),
    inference(resolution,[],[f7316,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f7316,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | spl12_15 ),
    inference(avatar_component_clause,[],[f7314])).

fof(f6059,plain,
    ( ~ spl12_10
    | spl12_14 ),
    inference(avatar_split_clause,[],[f181,f6057,f3641])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ) ),
    inference(subsumption_resolution,[],[f180,f19])).

fof(f180,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ) ),
    inference(subsumption_resolution,[],[f179,f22])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(sK0))
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(sK0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
      | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ) ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | sQ11_eqProxy(k5_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f23,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f23,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,(
    ~ sQ11_eqProxy(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f54,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sQ11_eqProxy(X0,X1)
      | sQ11_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f53])).

fof(f54,plain,(
    ~ sQ11_eqProxy(sK1,k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f21,f53])).

fof(f21,plain,(
    sK1 != k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f3736,plain,
    ( spl12_10
    | spl12_12 ),
    inference(avatar_split_clause,[],[f183,f3733,f3641])).

fof(f183,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f182,f19])).

fof(f182,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f178,f22])).

fof(f178,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(resolution,[],[f98,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | sQ11_eqProxy(k5_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f24,f53])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3648,plain,
    ( spl12_10
    | spl12_11 ),
    inference(avatar_split_clause,[],[f185,f3645,f3641])).

fof(f185,plain,
    ( r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f184,f19])).

fof(f184,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f177,f22])).

fof(f177,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) ),
    inference(resolution,[],[f98,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | sQ11_eqProxy(k5_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f25,f53])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.51  % (28478)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (28485)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (28469)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (28461)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (28471)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (28468)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (28466)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (28463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (28475)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (28488)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (28470)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (28465)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (28467)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (28492)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (28465)Refutation not found, incomplete strategy% (28465)------------------------------
% 0.20/0.53  % (28465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28465)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28465)Memory used [KB]: 10746
% 0.20/0.53  % (28465)Time elapsed: 0.134 s
% 0.20/0.53  % (28465)------------------------------
% 0.20/0.53  % (28465)------------------------------
% 1.38/0.53  % (28485)Refutation not found, incomplete strategy% (28485)------------------------------
% 1.38/0.53  % (28485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (28485)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (28485)Memory used [KB]: 10746
% 1.38/0.53  % (28485)Time elapsed: 0.062 s
% 1.38/0.53  % (28485)------------------------------
% 1.38/0.53  % (28485)------------------------------
% 1.38/0.53  % (28476)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.53  % (28486)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.53  % (28484)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.53  % (28473)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (28472)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.54  % (28490)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (28480)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.54  % (28481)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.54  % (28479)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (28477)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.54  % (28491)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (28483)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.55  % (28489)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.55  % (28474)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.56  % (28487)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.56  % (28482)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.09/0.65  % (28542)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.09/0.65  % (28541)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.43/0.83  % (28468)Time limit reached!
% 3.43/0.83  % (28468)------------------------------
% 3.43/0.83  % (28468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.43/0.83  % (28468)Termination reason: Time limit
% 3.43/0.83  
% 3.43/0.83  % (28468)Memory used [KB]: 9083
% 3.43/0.83  % (28468)Time elapsed: 0.436 s
% 3.43/0.83  % (28468)------------------------------
% 3.43/0.83  % (28468)------------------------------
% 3.65/0.90  % (28480)Time limit reached!
% 3.65/0.90  % (28480)------------------------------
% 3.65/0.90  % (28480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.90  % (28480)Termination reason: Time limit
% 3.65/0.90  
% 3.65/0.90  % (28480)Memory used [KB]: 14839
% 3.65/0.90  % (28480)Time elapsed: 0.510 s
% 3.65/0.90  % (28480)------------------------------
% 3.65/0.90  % (28480)------------------------------
% 3.65/0.90  % (28475)Time limit reached!
% 3.65/0.90  % (28475)------------------------------
% 3.65/0.90  % (28475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.90  % (28475)Termination reason: Time limit
% 3.65/0.90  
% 3.65/0.90  % (28475)Memory used [KB]: 9338
% 3.65/0.90  % (28475)Time elapsed: 0.508 s
% 3.65/0.90  % (28475)------------------------------
% 3.65/0.90  % (28475)------------------------------
% 3.65/0.91  % (28473)Time limit reached!
% 3.65/0.91  % (28473)------------------------------
% 3.65/0.91  % (28473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.91  % (28473)Termination reason: Time limit
% 3.65/0.91  % (28473)Termination phase: Saturation
% 3.65/0.91  
% 3.65/0.91  % (28473)Memory used [KB]: 17782
% 3.65/0.91  % (28473)Time elapsed: 0.520 s
% 3.65/0.91  % (28473)------------------------------
% 3.65/0.91  % (28473)------------------------------
% 3.65/0.92  % (28463)Time limit reached!
% 3.65/0.92  % (28463)------------------------------
% 3.65/0.92  % (28463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.92  % (28463)Termination reason: Time limit
% 3.65/0.92  
% 3.65/0.92  % (28463)Memory used [KB]: 8955
% 3.65/0.92  % (28463)Time elapsed: 0.503 s
% 3.65/0.92  % (28463)------------------------------
% 3.65/0.92  % (28463)------------------------------
% 3.65/0.92  % (28461)Time limit reached!
% 3.65/0.92  % (28461)------------------------------
% 3.65/0.92  % (28461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.65/0.92  % (28461)Termination reason: Time limit
% 3.65/0.92  
% 3.65/0.92  % (28461)Memory used [KB]: 4989
% 3.65/0.92  % (28461)Time elapsed: 0.526 s
% 3.65/0.92  % (28461)------------------------------
% 3.65/0.92  % (28461)------------------------------
% 4.24/0.95  % (28554)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.56/0.99  % (28479)Time limit reached!
% 4.56/0.99  % (28479)------------------------------
% 4.56/0.99  % (28479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/0.99  % (28479)Termination reason: Time limit
% 4.56/0.99  % (28479)Termination phase: Saturation
% 4.56/0.99  
% 4.56/0.99  % (28479)Memory used [KB]: 16375
% 4.56/0.99  % (28479)Time elapsed: 0.600 s
% 4.56/0.99  % (28479)------------------------------
% 4.56/0.99  % (28479)------------------------------
% 4.56/1.02  % (28491)Time limit reached!
% 4.56/1.02  % (28491)------------------------------
% 4.56/1.02  % (28491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.02  % (28491)Termination reason: Time limit
% 4.56/1.02  
% 4.56/1.02  % (28491)Memory used [KB]: 8827
% 4.56/1.02  % (28491)Time elapsed: 0.628 s
% 4.56/1.02  % (28491)------------------------------
% 4.56/1.02  % (28491)------------------------------
% 4.56/1.02  % (28470)Time limit reached!
% 4.56/1.02  % (28470)------------------------------
% 4.56/1.02  % (28470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.02  % (28470)Termination reason: Time limit
% 4.56/1.02  % (28470)Termination phase: Saturation
% 4.56/1.02  
% 4.56/1.02  % (28470)Memory used [KB]: 10490
% 4.56/1.02  % (28470)Time elapsed: 0.600 s
% 4.56/1.02  % (28470)------------------------------
% 4.56/1.02  % (28470)------------------------------
% 4.56/1.02  % (28557)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.56/1.03  % (28559)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.56/1.04  % (28555)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.56/1.04  % (28558)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.97/1.05  % (28556)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 6.07/1.14  % (28560)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.32/1.16  % (28562)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.32/1.17  % (28561)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.32/1.21  % (28484)Time limit reached!
% 6.32/1.21  % (28484)------------------------------
% 6.32/1.21  % (28484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.32/1.21  % (28484)Termination reason: Time limit
% 6.32/1.21  
% 6.32/1.21  % (28484)Memory used [KB]: 7803
% 6.32/1.21  % (28484)Time elapsed: 0.819 s
% 6.32/1.21  % (28484)------------------------------
% 6.32/1.21  % (28484)------------------------------
% 7.19/1.32  % (28555)Time limit reached!
% 7.19/1.32  % (28555)------------------------------
% 7.19/1.32  % (28555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.19/1.32  % (28555)Termination reason: Time limit
% 7.19/1.32  
% 7.19/1.32  % (28555)Memory used [KB]: 7036
% 7.19/1.32  % (28555)Time elapsed: 0.403 s
% 7.19/1.32  % (28555)------------------------------
% 7.19/1.32  % (28555)------------------------------
% 7.75/1.35  % (28563)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.75/1.36  % (28556)Time limit reached!
% 7.75/1.36  % (28556)------------------------------
% 7.75/1.36  % (28556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.75/1.36  % (28556)Termination reason: Time limit
% 7.75/1.36  % (28556)Termination phase: Saturation
% 7.75/1.36  
% 7.75/1.36  % (28556)Memory used [KB]: 13816
% 7.75/1.36  % (28556)Time elapsed: 0.400 s
% 7.75/1.36  % (28556)------------------------------
% 7.75/1.36  % (28556)------------------------------
% 8.62/1.48  % (28564)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.62/1.50  % (28565)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.39/1.64  % (28489)Time limit reached!
% 9.39/1.64  % (28489)------------------------------
% 9.39/1.64  % (28489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.39/1.64  % (28489)Termination reason: Time limit
% 9.39/1.64  
% 9.39/1.64  % (28489)Memory used [KB]: 25330
% 9.39/1.64  % (28489)Time elapsed: 1.224 s
% 9.39/1.64  % (28489)------------------------------
% 9.39/1.64  % (28489)------------------------------
% 11.10/1.76  % (28487)Time limit reached!
% 11.10/1.76  % (28487)------------------------------
% 11.10/1.76  % (28487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.10/1.76  % (28487)Termination reason: Time limit
% 11.10/1.76  
% 11.10/1.76  % (28487)Memory used [KB]: 25458
% 11.10/1.76  % (28487)Time elapsed: 1.322 s
% 11.10/1.76  % (28487)------------------------------
% 11.10/1.76  % (28487)------------------------------
% 11.10/1.76  % (28478)Time limit reached!
% 11.10/1.76  % (28478)------------------------------
% 11.10/1.76  % (28478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.10/1.76  % (28478)Termination reason: Time limit
% 11.10/1.76  % (28478)Termination phase: Saturation
% 11.10/1.76  
% 11.10/1.76  % (28478)Memory used [KB]: 19061
% 11.10/1.76  % (28478)Time elapsed: 1.316 s
% 11.10/1.76  % (28478)------------------------------
% 11.10/1.76  % (28478)------------------------------
% 11.10/1.81  % (28566)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.86/1.88  % (28564)Time limit reached!
% 11.86/1.88  % (28564)------------------------------
% 11.86/1.88  % (28564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.86/1.88  % (28564)Termination reason: Time limit
% 11.86/1.88  
% 11.86/1.88  % (28564)Memory used [KB]: 3454
% 11.86/1.88  % (28564)Time elapsed: 0.509 s
% 11.86/1.88  % (28564)------------------------------
% 11.86/1.88  % (28564)------------------------------
% 11.86/1.90  % (28490)Time limit reached!
% 11.86/1.90  % (28490)------------------------------
% 11.86/1.90  % (28490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.86/1.90  % (28490)Termination reason: Time limit
% 11.86/1.90  % (28490)Termination phase: Saturation
% 11.86/1.90  
% 11.86/1.90  % (28490)Memory used [KB]: 9850
% 11.86/1.90  % (28490)Time elapsed: 1.500 s
% 11.86/1.90  % (28490)------------------------------
% 11.86/1.90  % (28490)------------------------------
% 11.86/1.90  % (28568)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.86/1.92  % (28467)Time limit reached!
% 11.86/1.92  % (28467)------------------------------
% 11.86/1.92  % (28467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.86/1.92  % (28467)Termination reason: Time limit
% 11.86/1.92  
% 11.86/1.92  % (28467)Memory used [KB]: 19701
% 11.86/1.92  % (28467)Time elapsed: 1.512 s
% 11.86/1.92  % (28467)------------------------------
% 11.86/1.92  % (28467)------------------------------
% 11.86/1.92  % (28567)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 12.66/2.00  % (28476)Refutation found. Thanks to Tanya!
% 12.66/2.00  % SZS status Theorem for theBenchmark
% 12.66/2.00  % SZS output start Proof for theBenchmark
% 12.66/2.00  fof(f7435,plain,(
% 12.66/2.00    $false),
% 12.66/2.00    inference(avatar_sat_refutation,[],[f3648,f3736,f6059,f7331,f7361,f7424])).
% 12.66/2.00  fof(f7424,plain,(
% 12.66/2.00    ~spl12_10 | ~spl12_14),
% 12.66/2.00    inference(avatar_contradiction_clause,[],[f7423])).
% 12.66/2.00  fof(f7423,plain,(
% 12.66/2.00    $false | (~spl12_10 | ~spl12_14)),
% 12.66/2.00    inference(subsumption_resolution,[],[f7422,f3655])).
% 12.66/2.00  fof(f3655,plain,(
% 12.66/2.00    r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) | ~spl12_10),
% 12.66/2.00    inference(resolution,[],[f3643,f187])).
% 12.66/2.00  fof(f187,plain,(
% 12.66/2.00    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,sK0)) )),
% 12.66/2.00    inference(resolution,[],[f96,f52])).
% 12.66/2.00  fof(f52,plain,(
% 12.66/2.00    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 12.66/2.00    inference(equality_resolution,[],[f37])).
% 12.66/2.00  fof(f37,plain,(
% 12.66/2.00    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 12.66/2.00    inference(cnf_transformation,[],[f3])).
% 12.66/2.00  fof(f3,axiom,(
% 12.66/2.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 12.66/2.00  fof(f96,plain,(
% 12.66/2.00    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(X0,sK0)) )),
% 12.66/2.00    inference(resolution,[],[f20,f36])).
% 12.66/2.00  fof(f36,plain,(
% 12.66/2.00    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 12.66/2.00    inference(cnf_transformation,[],[f17])).
% 12.66/2.00  fof(f17,plain,(
% 12.66/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 12.66/2.00    inference(ennf_transformation,[],[f10])).
% 12.66/2.00  fof(f10,plain,(
% 12.66/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.66/2.00    inference(unused_predicate_definition_removal,[],[f1])).
% 12.66/2.00  fof(f1,axiom,(
% 12.66/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 12.66/2.00  fof(f20,plain,(
% 12.66/2.00    r1_tarski(k1_relat_1(sK1),sK0)),
% 12.66/2.00    inference(cnf_transformation,[],[f12])).
% 12.66/2.00  fof(f12,plain,(
% 12.66/2.00    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 12.66/2.00    inference(flattening,[],[f11])).
% 12.66/2.00  fof(f11,plain,(
% 12.66/2.00    ? [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 12.66/2.00    inference(ennf_transformation,[],[f9])).
% 12.66/2.00  fof(f9,negated_conjecture,(
% 12.66/2.00    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 12.66/2.00    inference(negated_conjecture,[],[f8])).
% 12.66/2.00  fof(f8,conjecture,(
% 12.66/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 12.66/2.00  fof(f3643,plain,(
% 12.66/2.00    r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~spl12_10),
% 12.66/2.00    inference(avatar_component_clause,[],[f3641])).
% 12.66/2.00  fof(f3641,plain,(
% 12.66/2.00    spl12_10 <=> r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 12.66/2.00  fof(f7422,plain,(
% 12.66/2.00    ~r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) | (~spl12_10 | ~spl12_14)),
% 12.66/2.00    inference(subsumption_resolution,[],[f7421,f22])).
% 12.66/2.00  fof(f22,plain,(
% 12.66/2.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 12.66/2.00    inference(cnf_transformation,[],[f6])).
% 12.66/2.00  fof(f6,axiom,(
% 12.66/2.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 12.66/2.00  fof(f7421,plain,(
% 12.66/2.00    ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) | (~spl12_10 | ~spl12_14)),
% 12.66/2.00    inference(subsumption_resolution,[],[f7404,f3643])).
% 12.66/2.00  fof(f7404,plain,(
% 12.66/2.00    ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK2(k6_relat_1(sK0),sK1,sK1),sK0) | ~spl12_14),
% 12.66/2.00    inference(resolution,[],[f6058,f48])).
% 12.66/2.00  fof(f48,plain,(
% 12.66/2.00    ( ! [X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))) )),
% 12.66/2.00    inference(equality_resolution,[],[f47])).
% 12.66/2.00  fof(f47,plain,(
% 12.66/2.00    ( ! [X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),X1) | k6_relat_1(X0) != X1) )),
% 12.66/2.00    inference(equality_resolution,[],[f34])).
% 12.66/2.00  fof(f34,plain,(
% 12.66/2.00    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | X2 != X3 | r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 12.66/2.00    inference(cnf_transformation,[],[f14])).
% 12.66/2.00  fof(f14,plain,(
% 12.66/2.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 12.66/2.00    inference(ennf_transformation,[],[f2])).
% 12.66/2.00  fof(f2,axiom,(
% 12.66/2.00    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 12.66/2.00  fof(f6058,plain,(
% 12.66/2.00    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1)) ) | ~spl12_14),
% 12.66/2.00    inference(avatar_component_clause,[],[f6057])).
% 12.66/2.00  fof(f6057,plain,(
% 12.66/2.00    spl12_14 <=> ! [X0] : (~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1))),
% 12.66/2.00    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 12.66/2.00  fof(f7361,plain,(
% 12.66/2.00    spl12_10 | ~spl12_11 | ~spl12_12 | ~spl12_15),
% 12.66/2.00    inference(avatar_contradiction_clause,[],[f7332])).
% 12.66/2.00  fof(f7332,plain,(
% 12.66/2.00    $false | (spl12_10 | ~spl12_11 | ~spl12_12 | ~spl12_15)),
% 12.66/2.00    inference(unit_resulting_resolution,[],[f3647,f3642,f3735,f7315,f260])).
% 12.66/2.00  fof(f260,plain,(
% 12.66/2.00    ( ! [X6,X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X6),k6_relat_1(X5)) | ~v1_relat_1(k5_relat_1(k6_relat_1(X5),sK1)) | r2_hidden(k4_tarski(X3,X4),sK1) | ~r2_hidden(k4_tarski(X6,X4),sK1)) )),
% 12.66/2.00    inference(subsumption_resolution,[],[f259,f19])).
% 12.66/2.00  fof(f19,plain,(
% 12.66/2.00    v1_relat_1(sK1)),
% 12.66/2.00    inference(cnf_transformation,[],[f12])).
% 12.66/2.00  fof(f259,plain,(
% 12.66/2.00    ( ! [X6,X4,X5,X3] : (r2_hidden(k4_tarski(X3,X4),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X5),sK1)) | ~r2_hidden(k4_tarski(X3,X6),k6_relat_1(X5)) | ~r2_hidden(k4_tarski(X6,X4),sK1)) )),
% 12.66/2.00    inference(subsumption_resolution,[],[f244,f22])).
% 12.66/2.00  fof(f244,plain,(
% 12.66/2.00    ( ! [X6,X4,X5,X3] : (r2_hidden(k4_tarski(X3,X4),sK1) | ~v1_relat_1(k6_relat_1(X5)) | ~v1_relat_1(sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(X5),sK1)) | ~r2_hidden(k4_tarski(X3,X6),k6_relat_1(X5)) | ~r2_hidden(k4_tarski(X6,X4),sK1)) )),
% 12.66/2.00    inference(resolution,[],[f70,f44])).
% 12.66/2.00  fof(f44,plain,(
% 12.66/2.00    ( ! [X4,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 12.66/2.00    inference(equality_resolution,[],[f28])).
% 12.66/2.00  fof(f28,plain,(
% 12.66/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 12.66/2.00    inference(cnf_transformation,[],[f13])).
% 12.66/2.00  fof(f13,plain,(
% 12.66/2.00    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 12.66/2.00    inference(ennf_transformation,[],[f4])).
% 12.66/2.00  fof(f4,axiom,(
% 12.66/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 12.66/2.00  fof(f70,plain,(
% 12.66/2.00    ( ! [X6,X7,X5] : (~r2_hidden(k4_tarski(X5,X6),k5_relat_1(k6_relat_1(X7),sK1)) | r2_hidden(k4_tarski(X5,X6),sK1)) )),
% 12.66/2.00    inference(resolution,[],[f19,f42])).
% 12.66/2.00  fof(f42,plain,(
% 12.66/2.00    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 12.66/2.00    inference(cnf_transformation,[],[f18])).
% 12.66/2.00  fof(f18,plain,(
% 12.66/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 12.66/2.00    inference(ennf_transformation,[],[f7])).
% 12.66/2.00  fof(f7,axiom,(
% 12.66/2.00    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 12.66/2.00  fof(f7315,plain,(
% 12.66/2.00    v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~spl12_15),
% 12.66/2.00    inference(avatar_component_clause,[],[f7314])).
% 12.66/2.00  fof(f7314,plain,(
% 12.66/2.00    spl12_15 <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 12.66/2.00    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 12.66/2.00  fof(f3735,plain,(
% 12.66/2.00    r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0)) | ~spl12_12),
% 12.66/2.00    inference(avatar_component_clause,[],[f3733])).
% 12.66/2.00  fof(f3733,plain,(
% 12.66/2.00    spl12_12 <=> r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0))),
% 12.66/2.00    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 12.66/2.00  fof(f3642,plain,(
% 12.66/2.00    ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | spl12_10),
% 12.66/2.00    inference(avatar_component_clause,[],[f3641])).
% 12.66/2.00  fof(f3647,plain,(
% 12.66/2.00    r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~spl12_11),
% 12.66/2.00    inference(avatar_component_clause,[],[f3645])).
% 12.66/2.00  fof(f3645,plain,(
% 12.66/2.00    spl12_11 <=> r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 12.66/2.00  fof(f7331,plain,(
% 12.66/2.00    spl12_15),
% 12.66/2.00    inference(avatar_contradiction_clause,[],[f7330])).
% 12.66/2.00  fof(f7330,plain,(
% 12.66/2.00    $false | spl12_15),
% 12.66/2.00    inference(subsumption_resolution,[],[f7329,f19])).
% 12.66/2.00  fof(f7329,plain,(
% 12.66/2.00    ~v1_relat_1(sK1) | spl12_15),
% 12.66/2.00    inference(subsumption_resolution,[],[f7324,f22])).
% 12.66/2.00  fof(f7324,plain,(
% 12.66/2.00    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl12_15),
% 12.66/2.00    inference(resolution,[],[f7316,f35])).
% 12.66/2.00  fof(f35,plain,(
% 12.66/2.00    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 12.66/2.00    inference(cnf_transformation,[],[f16])).
% 12.66/2.00  fof(f16,plain,(
% 12.66/2.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 12.66/2.00    inference(flattening,[],[f15])).
% 12.66/2.00  fof(f15,plain,(
% 12.66/2.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 12.66/2.00    inference(ennf_transformation,[],[f5])).
% 12.66/2.00  fof(f5,axiom,(
% 12.66/2.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 12.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 12.66/2.00  fof(f7316,plain,(
% 12.66/2.00    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | spl12_15),
% 12.66/2.00    inference(avatar_component_clause,[],[f7314])).
% 12.66/2.00  fof(f6059,plain,(
% 12.66/2.00    ~spl12_10 | spl12_14),
% 12.66/2.00    inference(avatar_split_clause,[],[f181,f6057,f3641])).
% 12.66/2.00  fof(f181,plain,(
% 12.66/2.00    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)) )),
% 12.66/2.00    inference(subsumption_resolution,[],[f180,f19])).
% 12.66/2.00  fof(f180,plain,(
% 12.66/2.00    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)) )),
% 12.66/2.00    inference(subsumption_resolution,[],[f179,f22])).
% 12.66/2.00  fof(f179,plain,(
% 12.66/2.00    ( ! [X0] : (~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)) )),
% 12.66/2.00    inference(duplicate_literal_removal,[],[f171])).
% 12.66/2.00  fof(f171,plain,(
% 12.66/2.00    ( ! [X0] : (~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),X0),k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | ~r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)) )),
% 12.66/2.00    inference(resolution,[],[f98,f57])).
% 12.66/2.00  fof(f57,plain,(
% 12.66/2.00    ( ! [X2,X0,X5,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) | ~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | sQ11_eqProxy(k5_relat_1(X0,X1),X2)) )),
% 12.66/2.00    inference(equality_proxy_replacement,[],[f23,f53])).
% 12.66/2.00  fof(f53,plain,(
% 12.66/2.00    ! [X1,X0] : (sQ11_eqProxy(X0,X1) <=> X0 = X1)),
% 12.66/2.00    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).
% 12.66/2.00  fof(f23,plain,(
% 12.66/2.00    ( ! [X2,X0,X5,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) | ~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 12.66/2.00    inference(cnf_transformation,[],[f13])).
% 12.66/2.00  fof(f98,plain,(
% 12.66/2.00    ~sQ11_eqProxy(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 12.66/2.00    inference(resolution,[],[f54,f65])).
% 12.66/2.00  fof(f65,plain,(
% 12.66/2.00    ( ! [X0,X1] : (~sQ11_eqProxy(X0,X1) | sQ11_eqProxy(X1,X0)) )),
% 12.66/2.00    inference(equality_proxy_axiom,[],[f53])).
% 12.66/2.00  fof(f54,plain,(
% 12.66/2.00    ~sQ11_eqProxy(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),
% 12.66/2.00    inference(equality_proxy_replacement,[],[f21,f53])).
% 12.66/2.00  fof(f21,plain,(
% 12.66/2.00    sK1 != k5_relat_1(k6_relat_1(sK0),sK1)),
% 12.66/2.00    inference(cnf_transformation,[],[f12])).
% 12.66/2.00  fof(f3736,plain,(
% 12.66/2.00    spl12_10 | spl12_12),
% 12.66/2.00    inference(avatar_split_clause,[],[f183,f3733,f3641])).
% 12.66/2.00  fof(f183,plain,(
% 12.66/2.00    r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(subsumption_resolution,[],[f182,f19])).
% 12.66/2.00  fof(f182,plain,(
% 12.66/2.00    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(subsumption_resolution,[],[f178,f22])).
% 12.66/2.00  fof(f178,plain,(
% 12.66/2.00    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(duplicate_literal_removal,[],[f172])).
% 12.66/2.00  fof(f172,plain,(
% 12.66/2.00    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK5(k6_relat_1(sK0),sK1,sK1)),k6_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(resolution,[],[f98,f56])).
% 12.66/2.00  fof(f56,plain,(
% 12.66/2.00    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK5(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | sQ11_eqProxy(k5_relat_1(X0,X1),X2)) )),
% 12.66/2.00    inference(equality_proxy_replacement,[],[f24,f53])).
% 12.66/2.00  fof(f24,plain,(
% 12.66/2.00    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK5(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 12.66/2.00    inference(cnf_transformation,[],[f13])).
% 12.66/2.00  fof(f3648,plain,(
% 12.66/2.00    spl12_10 | spl12_11),
% 12.66/2.00    inference(avatar_split_clause,[],[f185,f3645,f3641])).
% 12.66/2.00  fof(f185,plain,(
% 12.66/2.00    r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(subsumption_resolution,[],[f184,f19])).
% 12.66/2.00  fof(f184,plain,(
% 12.66/2.00    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(subsumption_resolution,[],[f177,f22])).
% 12.66/2.00  fof(f177,plain,(
% 12.66/2.00    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(duplicate_literal_removal,[],[f173])).
% 12.66/2.00  fof(f173,plain,(
% 12.66/2.00    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK5(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1) | r2_hidden(k4_tarski(sK2(k6_relat_1(sK0),sK1,sK1),sK3(k6_relat_1(sK0),sK1,sK1)),sK1)),
% 12.66/2.00    inference(resolution,[],[f98,f55])).
% 12.66/2.00  fof(f55,plain,(
% 12.66/2.00    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | sQ11_eqProxy(k5_relat_1(X0,X1),X2)) )),
% 12.66/2.00    inference(equality_proxy_replacement,[],[f25,f53])).
% 12.66/2.00  fof(f25,plain,(
% 12.66/2.00    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 12.66/2.00    inference(cnf_transformation,[],[f13])).
% 12.66/2.00  % SZS output end Proof for theBenchmark
% 12.66/2.00  % (28476)------------------------------
% 12.66/2.00  % (28476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.66/2.00  % (28476)Termination reason: Refutation
% 12.66/2.00  
% 12.66/2.00  % (28476)Memory used [KB]: 13304
% 12.66/2.00  % (28476)Time elapsed: 1.587 s
% 12.66/2.00  % (28476)------------------------------
% 12.66/2.00  % (28476)------------------------------
% 12.66/2.00  % (28458)Success in time 1.657 s
%------------------------------------------------------------------------------
