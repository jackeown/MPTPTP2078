%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:10 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 773 expanded)
%              Number of leaves         :   27 ( 266 expanded)
%              Depth                    :   29
%              Number of atoms          :  616 (3542 expanded)
%              Number of equality atoms :  143 (1288 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f723,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f77,f81,f85,f120,f144,f163,f174,f181,f186,f248,f266,f346,f365,f640,f649,f654,f720])).

fof(f720,plain,(
    spl8_26 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | spl8_26 ),
    inference(resolution,[],[f653,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f653,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl8_26
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f654,plain,
    ( ~ spl8_26
    | ~ spl8_1
    | spl8_25 ),
    inference(avatar_split_clause,[],[f650,f647,f57,f652])).

fof(f57,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f647,plain,
    ( spl8_25
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f650,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_1
    | spl8_25 ),
    inference(forward_demodulation,[],[f648,f323])).

fof(f323,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f648,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f647])).

fof(f649,plain,
    ( ~ spl8_5
    | ~ spl8_4
    | ~ spl8_25
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f393,f161,f75,f60,f647,f79,f83])).

fof(f83,plain,
    ( spl8_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f79,plain,
    ( spl8_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f60,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f75,plain,
    ( spl8_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f161,plain,
    ( spl8_10
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f393,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f392,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f392,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | sK1 != k1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_10 ),
    inference(superposition,[],[f33,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f33,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18])).

fof(f18,plain,
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

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f640,plain,
    ( spl8_1
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f624,f161,f142,f128,f57])).

fof(f128,plain,
    ( spl8_7
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f142,plain,
    ( spl8_9
  <=> ! [X6] :
        ( r2_hidden(sK3(k1_xboole_0,X6),k1_xboole_0)
        | r2_hidden(sK2(k1_xboole_0,X6),X6)
        | k2_relat_1(k1_xboole_0) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f624,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(resolution,[],[f622,f370])).

fof(f370,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f152,f162])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0,X0),X0)
        | k2_relat_1(k1_xboole_0) = X0 )
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(resolution,[],[f143,f129])).

fof(f129,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f143,plain,
    ( ! [X6] :
        ( r2_hidden(sK3(k1_xboole_0,X6),k1_xboole_0)
        | r2_hidden(sK2(k1_xboole_0,X6),X6)
        | k2_relat_1(k1_xboole_0) = X6 )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f622,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(resolution,[],[f621,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f621,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK6(sK1,X0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f617,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f617,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK6(sK1,X0))
      | ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK6(sK1,X0)) ) ),
    inference(trivial_inequality_removal,[],[f616])).

fof(f616,plain,(
    ! [X0] :
      ( sK1 != sK1
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK6(sK1,X0))
      | ~ v1_relat_1(sK6(sK1,X0)) ) ),
    inference(forward_demodulation,[],[f615,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f615,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 != k1_relat_1(sK6(sK1,X0))
      | ~ v1_funct_1(sK6(sK1,X0))
      | ~ v1_relat_1(sK6(sK1,X0)) ) ),
    inference(resolution,[],[f604,f33])).

fof(f604,plain,(
    ! [X3] :
      ( r1_tarski(k2_relat_1(sK6(sK1,X3)),sK0)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f43,f600])).

fof(f600,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ),
    inference(resolution,[],[f599,f44])).

fof(f599,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK6(sK1,X0))
      | sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ) ),
    inference(resolution,[],[f598,f45])).

fof(f598,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK6(sK1,X0))
      | ~ v1_relat_1(sK6(sK1,X0))
      | sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 ) ),
    inference(trivial_inequality_removal,[],[f597])).

fof(f597,plain,(
    ! [X0] :
      ( sK1 != sK1
      | sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0
      | ~ v1_relat_1(sK6(sK1,X0))
      | ~ v1_funct_1(sK6(sK1,X0)) ) ),
    inference(forward_demodulation,[],[f596,f46])).

fof(f596,plain,(
    ! [X0] :
      ( sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0
      | ~ v1_relat_1(sK6(sK1,X0))
      | ~ v1_funct_1(sK6(sK1,X0))
      | sK1 != k1_relat_1(sK6(sK1,X0)) ) ),
    inference(resolution,[],[f591,f463])).

fof(f463,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK5(k2_relat_1(X0),sK0)),sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK1 ) ),
    inference(inner_rewriting,[],[f462])).

fof(f462,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,sK5(k2_relat_1(X0),sK0)),k1_relat_1(X0))
      | k1_relat_1(X0) != sK1 ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,sK5(k2_relat_1(X0),sK0)),k1_relat_1(X0))
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f101,f33])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,sK5(k2_relat_1(X0),X1)),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f591,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0)),sK1)
      | sK5(k2_relat_1(sK6(sK1,X1)),sK0) = X1 ) ),
    inference(superposition,[],[f590,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f590,plain,(
    ! [X0] : sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0))) ),
    inference(equality_resolution,[],[f588])).

fof(f588,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k2_relat_1(sK6(X0,X1)),sK0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X0,X1),sK5(k2_relat_1(sK6(X0,X1)),sK0))) ) ),
    inference(global_subsumption,[],[f44,f587])).

fof(f587,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ v1_relat_1(sK6(X0,X1))
      | sK5(k2_relat_1(sK6(X0,X1)),sK0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X0,X1),sK5(k2_relat_1(sK6(X0,X1)),sK0))) ) ),
    inference(forward_demodulation,[],[f584,f46])).

fof(f584,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK6(X0,X1))
      | sK5(k2_relat_1(sK6(X0,X1)),sK0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X0,X1),sK5(k2_relat_1(sK6(X0,X1)),sK0)))
      | sK1 != k1_relat_1(sK6(X0,X1)) ) ),
    inference(resolution,[],[f583,f45])).

fof(f583,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK5(k2_relat_1(X0),sK0) = k1_funct_1(X0,sK4(X0,sK5(k2_relat_1(X0),sK0)))
      | k1_relat_1(X0) != sK1 ) ),
    inference(duplicate_literal_removal,[],[f581])).

fof(f581,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK5(k2_relat_1(X0),sK0) = k1_funct_1(X0,sK4(X0,sK5(k2_relat_1(X0),sK0)))
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f104,f33])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK5(k2_relat_1(X0),X1) = k1_funct_1(X0,sK4(X0,sK5(k2_relat_1(X0),X1))) ) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f365,plain,
    ( ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f301,f363])).

fof(f363,plain,
    ( ! [X0,X1] : r1_tarski(X0,X1)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f43,f265])).

fof(f265,plain,
    ( ! [X2,X1] : r2_hidden(X1,X2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_18
  <=> ! [X1,X2] : r2_hidden(X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f301,plain,
    ( ! [X2] : ~ r1_tarski(k2_relat_1(X2),sK0)
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f285,f296])).

fof(f296,plain,
    ( ! [X2] : v1_funct_1(X2)
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f224,f180])).

fof(f180,plain,
    ( ! [X1] : k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X1)) = X1
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl8_13
  <=> ! [X1] : k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f224,plain,
    ( ! [X2] : v1_funct_1(k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)))
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(superposition,[],[f45,f189])).

fof(f189,plain,
    ( ! [X0,X1] : k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X0)) = X1
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f187,f180])).

fof(f187,plain,
    ( ! [X0,X1] : k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X0)))) = X1
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(resolution,[],[f185,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X0))) = X1 )
    | ~ spl8_6 ),
    inference(resolution,[],[f119,f70])).

fof(f70,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | k1_funct_1(k1_xboole_0,X2) = X1 ) ),
    inference(superposition,[],[f47,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK6(X0,X1) ) ),
    inference(superposition,[],[f65,f46])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(sK6(X0,X1))
      | k1_xboole_0 = sK6(X0,X1) ) ),
    inference(resolution,[],[f34,f44])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f119,plain,
    ( ! [X6] :
        ( r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0)
        | ~ r2_hidden(X6,k1_xboole_0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_6
  <=> ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f185,plain,
    ( ! [X2] : r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_14
  <=> ! [X2] : r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f285,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | ~ v1_funct_1(X2) )
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f239,f275])).

fof(f275,plain,
    ( ! [X2] : v1_relat_1(X2)
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f223,f180])).

fof(f223,plain,
    ( ! [X2] : v1_relat_1(k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)))
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(superposition,[],[f44,f189])).

fof(f239,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f33,f198])).

fof(f198,plain,
    ( ! [X2,X1] : X1 = X2
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(superposition,[],[f189,f189])).

fof(f346,plain,
    ( ~ spl8_8
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f132,f262])).

fof(f262,plain,
    ( ! [X0,X3] : ~ r2_hidden(X3,X0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl8_17
  <=> ! [X3,X0] : ~ r2_hidden(X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f132,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_8
  <=> ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f266,plain,
    ( spl8_17
    | spl8_18
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f259,f184,f179,f118,f264,f261])).

fof(f259,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X1,X2)
        | ~ r2_hidden(X3,X0) )
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f212,f180])).

fof(f212,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X1,k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)))
        | ~ r2_hidden(X3,X0) )
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(superposition,[],[f146,f189])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_relat_1(sK6(X1,X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f124,f44])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK6(X1,X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X0,k2_relat_1(sK6(X1,X0))) ) ),
    inference(resolution,[],[f91,f45])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK6(X0,X1))
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | ~ v1_relat_1(sK6(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f88,f46])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK6(X0,X1)))
      | ~ r2_hidden(X2,k1_relat_1(sK6(X0,X1)))
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f53,f47])).

fof(f53,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f248,plain,
    ( spl8_1
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl8_1
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f58,f198])).

fof(f58,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f186,plain,
    ( ~ spl8_5
    | ~ spl8_4
    | spl8_14
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f182,f131,f75,f184,f79,f83])).

fof(f182,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f177,f76])).

fof(f177,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(k1_xboole_0,X2),k1_relat_1(k1_xboole_0))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f132,f55])).

fof(f181,plain,
    ( ~ spl8_5
    | ~ spl8_4
    | spl8_13
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f176,f131,f179,f79,f83])).

fof(f176,plain,
    ( ! [X1] :
        ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X1)) = X1
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f132,f54])).

fof(f174,plain,
    ( spl8_8
    | spl8_7 ),
    inference(avatar_split_clause,[],[f173,f128,f131])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X0,k2_relat_1(k1_xboole_0)) ) ),
    inference(global_subsumption,[],[f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f146,f68])).

fof(f163,plain,
    ( spl8_10
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f155,f142,f128,f161])).

fof(f155,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(resolution,[],[f152,f129])).

fof(f144,plain,
    ( ~ spl8_5
    | ~ spl8_4
    | spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f137,f75,f142,f79,f83])).

fof(f137,plain,
    ( ! [X6] :
        ( r2_hidden(sK3(k1_xboole_0,X6),k1_xboole_0)
        | k2_relat_1(k1_xboole_0) = X6
        | r2_hidden(sK2(k1_xboole_0,X6),X6)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_3 ),
    inference(superposition,[],[f39,f76])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,
    ( ~ spl8_5
    | spl8_6
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f115,f79,f75,f118,f83])).

fof(f115,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f114,f76])).

fof(f114,plain,
    ( ! [X6] :
        ( r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ r2_hidden(X6,k1_relat_1(k1_xboole_0)) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f109,f76])).

fof(f109,plain,
    ( ! [X6] :
        ( r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0)
        | ~ r2_hidden(X6,k1_relat_1(k1_xboole_0)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f103,f80])).

fof(f80,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | r2_hidden(sK4(X2,k1_funct_1(X2,X3)),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,k1_funct_1(X2,X3)),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f55,f53])).

fof(f85,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f73,f83])).

fof(f73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f44,f68])).

fof(f81,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f72,f79])).

fof(f72,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f45,f68])).

fof(f77,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f71,f75])).

fof(f71,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f68])).

fof(f62,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f32,f60,f57])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (6354)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (6346)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (6343)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (6362)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (6355)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (6351)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (6344)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (6362)Refutation not found, incomplete strategy% (6362)------------------------------
% 0.22/0.52  % (6362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6362)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6362)Memory used [KB]: 10746
% 0.22/0.52  % (6362)Time elapsed: 0.110 s
% 0.22/0.52  % (6362)------------------------------
% 0.22/0.52  % (6362)------------------------------
% 0.22/0.52  % (6365)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (6352)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (6344)Refutation not found, incomplete strategy% (6344)------------------------------
% 0.22/0.53  % (6344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6344)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6344)Memory used [KB]: 10618
% 0.22/0.53  % (6344)Time elapsed: 0.116 s
% 0.22/0.53  % (6344)------------------------------
% 0.22/0.53  % (6344)------------------------------
% 0.22/0.53  % (6348)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (6347)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (6358)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (6359)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (6345)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (6359)Refutation not found, incomplete strategy% (6359)------------------------------
% 0.22/0.54  % (6359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6359)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6359)Memory used [KB]: 10746
% 0.22/0.54  % (6359)Time elapsed: 0.130 s
% 0.22/0.54  % (6359)------------------------------
% 0.22/0.54  % (6359)------------------------------
% 0.22/0.54  % (6349)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (6369)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (6363)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (6368)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (6356)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (6357)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (6361)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (6360)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (6342)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (6366)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (6352)Refutation not found, incomplete strategy% (6352)------------------------------
% 0.22/0.55  % (6352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6352)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6352)Memory used [KB]: 10618
% 0.22/0.55  % (6352)Time elapsed: 0.139 s
% 0.22/0.55  % (6352)------------------------------
% 0.22/0.55  % (6352)------------------------------
% 0.22/0.55  % (6371)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (6370)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (6353)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (6367)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.56  % (6364)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.56  % (6364)Refutation not found, incomplete strategy% (6364)------------------------------
% 1.53/0.56  % (6364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (6364)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (6364)Memory used [KB]: 10618
% 1.53/0.56  % (6364)Time elapsed: 0.150 s
% 1.53/0.56  % (6364)------------------------------
% 1.53/0.56  % (6364)------------------------------
% 1.53/0.56  % (6350)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.56  % (6363)Refutation not found, incomplete strategy% (6363)------------------------------
% 1.53/0.56  % (6363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (6363)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (6363)Memory used [KB]: 1663
% 1.53/0.56  % (6363)Time elapsed: 0.152 s
% 1.53/0.56  % (6363)------------------------------
% 1.53/0.56  % (6363)------------------------------
% 1.53/0.56  % (6350)Refutation not found, incomplete strategy% (6350)------------------------------
% 1.53/0.56  % (6350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (6350)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (6350)Memory used [KB]: 10618
% 1.53/0.56  % (6350)Time elapsed: 0.151 s
% 1.53/0.56  % (6350)------------------------------
% 1.53/0.56  % (6350)------------------------------
% 1.64/0.59  % (6361)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  fof(f723,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(avatar_sat_refutation,[],[f62,f77,f81,f85,f120,f144,f163,f174,f181,f186,f248,f266,f346,f365,f640,f649,f654,f720])).
% 1.64/0.59  fof(f720,plain,(
% 1.64/0.59    spl8_26),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f719])).
% 1.64/0.59  fof(f719,plain,(
% 1.64/0.59    $false | spl8_26),
% 1.64/0.59    inference(resolution,[],[f653,f64])).
% 1.64/0.59  fof(f64,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f63])).
% 1.64/0.59  fof(f63,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.64/0.59    inference(resolution,[],[f43,f42])).
% 1.64/0.59  fof(f42,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f27])).
% 1.64/0.59  fof(f27,plain,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f26])).
% 1.64/0.59  fof(f26,plain,(
% 1.64/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f15,plain,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f8])).
% 1.64/0.59  fof(f8,plain,(
% 1.64/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.64/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 1.64/0.59  fof(f1,axiom,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.59  fof(f43,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f27])).
% 1.64/0.59  fof(f653,plain,(
% 1.64/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl8_26),
% 1.64/0.59    inference(avatar_component_clause,[],[f652])).
% 1.64/0.59  fof(f652,plain,(
% 1.64/0.59    spl8_26 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.64/0.59  fof(f654,plain,(
% 1.64/0.59    ~spl8_26 | ~spl8_1 | spl8_25),
% 1.64/0.59    inference(avatar_split_clause,[],[f650,f647,f57,f652])).
% 1.64/0.59  fof(f57,plain,(
% 1.64/0.59    spl8_1 <=> k1_xboole_0 = sK0),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.64/0.59  fof(f647,plain,(
% 1.64/0.59    spl8_25 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.64/0.59  fof(f650,plain,(
% 1.64/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_1 | spl8_25)),
% 1.64/0.59    inference(forward_demodulation,[],[f648,f323])).
% 1.64/0.59  fof(f323,plain,(
% 1.64/0.59    k1_xboole_0 = sK0 | ~spl8_1),
% 1.64/0.59    inference(avatar_component_clause,[],[f57])).
% 1.64/0.59  fof(f648,plain,(
% 1.64/0.59    ~r1_tarski(k1_xboole_0,sK0) | spl8_25),
% 1.64/0.59    inference(avatar_component_clause,[],[f647])).
% 1.64/0.59  fof(f649,plain,(
% 1.64/0.59    ~spl8_5 | ~spl8_4 | ~spl8_25 | ~spl8_2 | ~spl8_3 | ~spl8_10),
% 1.64/0.59    inference(avatar_split_clause,[],[f393,f161,f75,f60,f647,f79,f83])).
% 1.64/0.59  fof(f83,plain,(
% 1.64/0.59    spl8_5 <=> v1_relat_1(k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.64/0.59  fof(f79,plain,(
% 1.64/0.59    spl8_4 <=> v1_funct_1(k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.64/0.59  fof(f60,plain,(
% 1.64/0.59    spl8_2 <=> k1_xboole_0 = sK1),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.64/0.59  fof(f75,plain,(
% 1.64/0.59    spl8_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.64/0.59  fof(f161,plain,(
% 1.64/0.59    spl8_10 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.64/0.59  fof(f393,plain,(
% 1.64/0.59    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl8_3 | ~spl8_10)),
% 1.64/0.59    inference(forward_demodulation,[],[f392,f76])).
% 1.64/0.59  fof(f76,plain,(
% 1.64/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_3),
% 1.64/0.59    inference(avatar_component_clause,[],[f75])).
% 1.64/0.59  fof(f392,plain,(
% 1.64/0.59    ~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl8_10),
% 1.64/0.59    inference(superposition,[],[f33,f162])).
% 1.64/0.59  fof(f162,plain,(
% 1.64/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_10),
% 1.64/0.59    inference(avatar_component_clause,[],[f161])).
% 1.64/0.59  fof(f33,plain,(
% 1.64/0.59    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f19])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18])).
% 1.64/0.59  fof(f18,plain,(
% 1.64/0.59    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f10,plain,(
% 1.64/0.59    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.64/0.59    inference(flattening,[],[f9])).
% 1.64/0.59  fof(f9,plain,(
% 1.64/0.59    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f7])).
% 1.64/0.59  fof(f7,negated_conjecture,(
% 1.64/0.59    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.64/0.59    inference(negated_conjecture,[],[f6])).
% 1.64/0.59  fof(f6,conjecture,(
% 1.64/0.59    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.64/0.59  fof(f640,plain,(
% 1.64/0.59    spl8_1 | ~spl8_7 | ~spl8_9 | ~spl8_10),
% 1.64/0.59    inference(avatar_split_clause,[],[f624,f161,f142,f128,f57])).
% 1.64/0.59  fof(f128,plain,(
% 1.64/0.59    spl8_7 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.64/0.59  fof(f142,plain,(
% 1.64/0.59    spl8_9 <=> ! [X6] : (r2_hidden(sK3(k1_xboole_0,X6),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X6),X6) | k2_relat_1(k1_xboole_0) = X6)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.64/0.59  fof(f624,plain,(
% 1.64/0.59    k1_xboole_0 = sK0 | (~spl8_7 | ~spl8_9 | ~spl8_10)),
% 1.64/0.59    inference(resolution,[],[f622,f370])).
% 1.64/0.59  fof(f370,plain,(
% 1.64/0.59    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) ) | (~spl8_7 | ~spl8_9 | ~spl8_10)),
% 1.64/0.59    inference(forward_demodulation,[],[f152,f162])).
% 1.64/0.59  fof(f152,plain,(
% 1.64/0.59    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | k2_relat_1(k1_xboole_0) = X0) ) | (~spl8_7 | ~spl8_9)),
% 1.64/0.59    inference(resolution,[],[f143,f129])).
% 1.64/0.59  fof(f129,plain,(
% 1.64/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl8_7),
% 1.64/0.59    inference(avatar_component_clause,[],[f128])).
% 1.64/0.59  fof(f143,plain,(
% 1.64/0.59    ( ! [X6] : (r2_hidden(sK3(k1_xboole_0,X6),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X6),X6) | k2_relat_1(k1_xboole_0) = X6) ) | ~spl8_9),
% 1.64/0.59    inference(avatar_component_clause,[],[f142])).
% 1.64/0.59  fof(f622,plain,(
% 1.64/0.59    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.64/0.59    inference(resolution,[],[f621,f44])).
% 1.64/0.59  fof(f44,plain,(
% 1.64/0.59    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f29,plain,(
% 1.64/0.59    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f28])).
% 1.64/0.59  fof(f28,plain,(
% 1.64/0.59    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f16,plain,(
% 1.64/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.64/0.59    inference(ennf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.64/0.59  fof(f621,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_relat_1(sK6(sK1,X0)) | ~r2_hidden(X0,sK0)) )),
% 1.64/0.59    inference(resolution,[],[f617,f45])).
% 1.64/0.59  fof(f45,plain,(
% 1.64/0.59    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f617,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_funct_1(sK6(sK1,X0)) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK6(sK1,X0))) )),
% 1.64/0.59    inference(trivial_inequality_removal,[],[f616])).
% 1.64/0.59  fof(f616,plain,(
% 1.64/0.59    ( ! [X0] : (sK1 != sK1 | ~r2_hidden(X0,sK0) | ~v1_funct_1(sK6(sK1,X0)) | ~v1_relat_1(sK6(sK1,X0))) )),
% 1.64/0.59    inference(forward_demodulation,[],[f615,f46])).
% 1.64/0.59  fof(f46,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f615,plain,(
% 1.64/0.59    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 != k1_relat_1(sK6(sK1,X0)) | ~v1_funct_1(sK6(sK1,X0)) | ~v1_relat_1(sK6(sK1,X0))) )),
% 1.64/0.59    inference(resolution,[],[f604,f33])).
% 1.64/0.59  fof(f604,plain,(
% 1.64/0.59    ( ! [X3] : (r1_tarski(k2_relat_1(sK6(sK1,X3)),sK0) | ~r2_hidden(X3,sK0)) )),
% 1.64/0.59    inference(superposition,[],[f43,f600])).
% 1.64/0.59  fof(f600,plain,(
% 1.64/0.59    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 1.64/0.59    inference(resolution,[],[f599,f44])).
% 1.64/0.59  fof(f599,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_relat_1(sK6(sK1,X0)) | sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 1.64/0.59    inference(resolution,[],[f598,f45])).
% 1.64/0.59  fof(f598,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_funct_1(sK6(sK1,X0)) | ~v1_relat_1(sK6(sK1,X0)) | sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0) )),
% 1.64/0.59    inference(trivial_inequality_removal,[],[f597])).
% 1.64/0.59  fof(f597,plain,(
% 1.64/0.59    ( ! [X0] : (sK1 != sK1 | sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 | ~v1_relat_1(sK6(sK1,X0)) | ~v1_funct_1(sK6(sK1,X0))) )),
% 1.64/0.59    inference(forward_demodulation,[],[f596,f46])).
% 1.64/0.59  fof(f596,plain,(
% 1.64/0.59    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = X0 | ~v1_relat_1(sK6(sK1,X0)) | ~v1_funct_1(sK6(sK1,X0)) | sK1 != k1_relat_1(sK6(sK1,X0))) )),
% 1.64/0.59    inference(resolution,[],[f591,f463])).
% 1.64/0.59  fof(f463,plain,(
% 1.64/0.59    ( ! [X0] : (r2_hidden(sK4(X0,sK5(k2_relat_1(X0),sK0)),sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK1) )),
% 1.64/0.59    inference(inner_rewriting,[],[f462])).
% 1.64/0.59  fof(f462,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,sK5(k2_relat_1(X0),sK0)),k1_relat_1(X0)) | k1_relat_1(X0) != sK1) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f460])).
% 1.64/0.59  fof(f460,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,sK5(k2_relat_1(X0),sK0)),k1_relat_1(X0)) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(resolution,[],[f101,f33])).
% 1.64/0.59  fof(f101,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,sK5(k2_relat_1(X0),X1)),k1_relat_1(X0))) )),
% 1.64/0.59    inference(resolution,[],[f55,f42])).
% 1.64/0.59  fof(f55,plain,(
% 1.64/0.59    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f36])).
% 1.64/0.59  fof(f36,plain,(
% 1.64/0.59    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f25,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(rectify,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(nnf_transformation,[],[f14])).
% 1.64/0.59  fof(f14,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f13])).
% 1.64/0.59  fof(f13,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f3])).
% 1.64/0.59  fof(f3,axiom,(
% 1.64/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.64/0.59  fof(f591,plain,(
% 1.64/0.59    ( ! [X1] : (~r2_hidden(sK4(sK6(sK1,X1),sK5(k2_relat_1(sK6(sK1,X1)),sK0)),sK1) | sK5(k2_relat_1(sK6(sK1,X1)),sK0) = X1) )),
% 1.64/0.59    inference(superposition,[],[f590,f47])).
% 1.64/0.59  fof(f47,plain,(
% 1.64/0.59    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f590,plain,(
% 1.64/0.59    ( ! [X0] : (sK5(k2_relat_1(sK6(sK1,X0)),sK0) = k1_funct_1(sK6(sK1,X0),sK4(sK6(sK1,X0),sK5(k2_relat_1(sK6(sK1,X0)),sK0)))) )),
% 1.64/0.59    inference(equality_resolution,[],[f588])).
% 1.64/0.59  fof(f588,plain,(
% 1.64/0.59    ( ! [X0,X1] : (sK1 != X0 | sK5(k2_relat_1(sK6(X0,X1)),sK0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X0,X1),sK5(k2_relat_1(sK6(X0,X1)),sK0)))) )),
% 1.64/0.59    inference(global_subsumption,[],[f44,f587])).
% 1.64/0.59  fof(f587,plain,(
% 1.64/0.59    ( ! [X0,X1] : (sK1 != X0 | ~v1_relat_1(sK6(X0,X1)) | sK5(k2_relat_1(sK6(X0,X1)),sK0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X0,X1),sK5(k2_relat_1(sK6(X0,X1)),sK0)))) )),
% 1.64/0.59    inference(forward_demodulation,[],[f584,f46])).
% 1.64/0.59  fof(f584,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~v1_relat_1(sK6(X0,X1)) | sK5(k2_relat_1(sK6(X0,X1)),sK0) = k1_funct_1(sK6(X0,X1),sK4(sK6(X0,X1),sK5(k2_relat_1(sK6(X0,X1)),sK0))) | sK1 != k1_relat_1(sK6(X0,X1))) )),
% 1.64/0.59    inference(resolution,[],[f583,f45])).
% 1.64/0.59  fof(f583,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK5(k2_relat_1(X0),sK0) = k1_funct_1(X0,sK4(X0,sK5(k2_relat_1(X0),sK0))) | k1_relat_1(X0) != sK1) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f581])).
% 1.64/0.59  fof(f581,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK5(k2_relat_1(X0),sK0) = k1_funct_1(X0,sK4(X0,sK5(k2_relat_1(X0),sK0))) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(resolution,[],[f104,f33])).
% 1.64/0.59  fof(f104,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK5(k2_relat_1(X0),X1) = k1_funct_1(X0,sK4(X0,sK5(k2_relat_1(X0),X1)))) )),
% 1.64/0.59    inference(resolution,[],[f54,f42])).
% 1.64/0.59  fof(f54,plain,(
% 1.64/0.59    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK4(X0,X5)) = X5 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f37])).
% 1.64/0.59  fof(f37,plain,(
% 1.64/0.59    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f365,plain,(
% 1.64/0.59    ~spl8_6 | ~spl8_13 | ~spl8_14 | ~spl8_18),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f364])).
% 1.64/0.59  fof(f364,plain,(
% 1.64/0.59    $false | (~spl8_6 | ~spl8_13 | ~spl8_14 | ~spl8_18)),
% 1.64/0.59    inference(subsumption_resolution,[],[f301,f363])).
% 1.64/0.59  fof(f363,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1)) ) | ~spl8_18),
% 1.64/0.59    inference(subsumption_resolution,[],[f43,f265])).
% 1.64/0.59  fof(f265,plain,(
% 1.64/0.59    ( ! [X2,X1] : (r2_hidden(X1,X2)) ) | ~spl8_18),
% 1.64/0.59    inference(avatar_component_clause,[],[f264])).
% 1.64/0.59  fof(f264,plain,(
% 1.64/0.59    spl8_18 <=> ! [X1,X2] : r2_hidden(X1,X2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.64/0.59  fof(f301,plain,(
% 1.64/0.59    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(subsumption_resolution,[],[f285,f296])).
% 1.64/0.59  fof(f296,plain,(
% 1.64/0.59    ( ! [X2] : (v1_funct_1(X2)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(forward_demodulation,[],[f224,f180])).
% 1.64/0.59  fof(f180,plain,(
% 1.64/0.59    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X1)) = X1) ) | ~spl8_13),
% 1.64/0.59    inference(avatar_component_clause,[],[f179])).
% 1.64/0.59  fof(f179,plain,(
% 1.64/0.59    spl8_13 <=> ! [X1] : k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X1)) = X1),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.64/0.59  fof(f224,plain,(
% 1.64/0.59    ( ! [X2] : (v1_funct_1(k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)))) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(superposition,[],[f45,f189])).
% 1.64/0.59  fof(f189,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X0)) = X1) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(forward_demodulation,[],[f187,f180])).
% 1.64/0.59  fof(f187,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X0)))) = X1) ) | (~spl8_6 | ~spl8_14)),
% 1.64/0.59    inference(resolution,[],[f185,f121])).
% 1.64/0.59  fof(f121,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X0))) = X1) ) | ~spl8_6),
% 1.64/0.59    inference(resolution,[],[f119,f70])).
% 1.64/0.59  fof(f70,plain,(
% 1.64/0.59    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | k1_funct_1(k1_xboole_0,X2) = X1) )),
% 1.64/0.59    inference(superposition,[],[f47,f68])).
% 1.64/0.59  fof(f68,plain,(
% 1.64/0.59    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f67])).
% 1.64/0.59  fof(f67,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK6(X0,X1)) )),
% 1.64/0.59    inference(superposition,[],[f65,f46])).
% 1.64/0.59  fof(f65,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK6(X0,X1)) | k1_xboole_0 = sK6(X0,X1)) )),
% 1.64/0.59    inference(resolution,[],[f34,f44])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f12])).
% 1.64/0.59  fof(f12,plain,(
% 1.64/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(flattening,[],[f11])).
% 1.64/0.59  fof(f11,plain,(
% 1.64/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f2])).
% 1.64/0.59  fof(f2,axiom,(
% 1.64/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.64/0.59  fof(f119,plain,(
% 1.64/0.59    ( ! [X6] : (r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) ) | ~spl8_6),
% 1.64/0.59    inference(avatar_component_clause,[],[f118])).
% 1.64/0.59  fof(f118,plain,(
% 1.64/0.59    spl8_6 <=> ! [X6] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.64/0.59  fof(f185,plain,(
% 1.64/0.59    ( ! [X2] : (r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0)) ) | ~spl8_14),
% 1.64/0.59    inference(avatar_component_clause,[],[f184])).
% 1.64/0.59  fof(f184,plain,(
% 1.64/0.59    spl8_14 <=> ! [X2] : r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.64/0.59  fof(f285,plain,(
% 1.64/0.59    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(subsumption_resolution,[],[f239,f275])).
% 1.64/0.59  fof(f275,plain,(
% 1.64/0.59    ( ! [X2] : (v1_relat_1(X2)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(forward_demodulation,[],[f223,f180])).
% 1.64/0.59  fof(f223,plain,(
% 1.64/0.59    ( ! [X2] : (v1_relat_1(k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)))) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(superposition,[],[f44,f189])).
% 1.64/0.59  fof(f239,plain,(
% 1.64/0.59    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(subsumption_resolution,[],[f33,f198])).
% 1.64/0.59  fof(f198,plain,(
% 1.64/0.59    ( ! [X2,X1] : (X1 = X2) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(superposition,[],[f189,f189])).
% 1.64/0.59  fof(f346,plain,(
% 1.64/0.59    ~spl8_8 | ~spl8_17),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f325])).
% 1.64/0.59  fof(f325,plain,(
% 1.64/0.59    $false | (~spl8_8 | ~spl8_17)),
% 1.64/0.59    inference(subsumption_resolution,[],[f132,f262])).
% 1.64/0.59  fof(f262,plain,(
% 1.64/0.59    ( ! [X0,X3] : (~r2_hidden(X3,X0)) ) | ~spl8_17),
% 1.64/0.59    inference(avatar_component_clause,[],[f261])).
% 1.64/0.59  fof(f261,plain,(
% 1.64/0.59    spl8_17 <=> ! [X3,X0] : ~r2_hidden(X3,X0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.64/0.59  fof(f132,plain,(
% 1.64/0.59    ( ! [X0] : (r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl8_8),
% 1.64/0.59    inference(avatar_component_clause,[],[f131])).
% 1.64/0.59  fof(f131,plain,(
% 1.64/0.59    spl8_8 <=> ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.64/0.59  fof(f266,plain,(
% 1.64/0.59    spl8_17 | spl8_18 | ~spl8_6 | ~spl8_13 | ~spl8_14),
% 1.64/0.59    inference(avatar_split_clause,[],[f259,f184,f179,f118,f264,f261])).
% 1.64/0.59  fof(f259,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X3,X0)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(forward_demodulation,[],[f212,f180])).
% 1.64/0.59  fof(f212,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2))) | ~r2_hidden(X3,X0)) ) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(superposition,[],[f146,f189])).
% 1.64/0.59  fof(f146,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_relat_1(sK6(X1,X2))) | ~r2_hidden(X0,X1)) )),
% 1.64/0.59    inference(resolution,[],[f124,f44])).
% 1.64/0.59  fof(f124,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(sK6(X1,X0)) | ~r2_hidden(X2,X1) | r2_hidden(X0,k2_relat_1(sK6(X1,X0)))) )),
% 1.64/0.59    inference(resolution,[],[f91,f45])).
% 1.64/0.59  fof(f91,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(sK6(X0,X1)) | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,X0) | ~v1_relat_1(sK6(X0,X1))) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f90])).
% 1.64/0.59  fof(f90,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.64/0.59    inference(forward_demodulation,[],[f88,f46])).
% 1.64/0.59  fof(f88,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK6(X0,X1))) | ~r2_hidden(X2,k1_relat_1(sK6(X0,X1))) | ~v1_funct_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.64/0.59    inference(superposition,[],[f53,f47])).
% 1.64/0.59  fof(f53,plain,(
% 1.64/0.59    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f52])).
% 1.64/0.59  fof(f52,plain,(
% 1.64/0.59    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f38])).
% 1.64/0.59  fof(f38,plain,(
% 1.64/0.59    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f248,plain,(
% 1.64/0.59    spl8_1 | ~spl8_6 | ~spl8_13 | ~spl8_14),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f246])).
% 1.64/0.59  fof(f246,plain,(
% 1.64/0.59    $false | (spl8_1 | ~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.64/0.59    inference(subsumption_resolution,[],[f58,f198])).
% 1.64/0.59  fof(f58,plain,(
% 1.64/0.59    k1_xboole_0 != sK0 | spl8_1),
% 1.64/0.59    inference(avatar_component_clause,[],[f57])).
% 1.64/0.59  fof(f186,plain,(
% 1.64/0.59    ~spl8_5 | ~spl8_4 | spl8_14 | ~spl8_3 | ~spl8_8),
% 1.64/0.59    inference(avatar_split_clause,[],[f182,f131,f75,f184,f79,f83])).
% 1.64/0.59  fof(f182,plain,(
% 1.64/0.59    ( ! [X2] : (r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl8_3 | ~spl8_8)),
% 1.64/0.59    inference(forward_demodulation,[],[f177,f76])).
% 1.64/0.59  fof(f177,plain,(
% 1.64/0.59    ( ! [X2] : (r2_hidden(sK4(k1_xboole_0,X2),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_8),
% 1.64/0.59    inference(resolution,[],[f132,f55])).
% 1.64/0.59  fof(f181,plain,(
% 1.64/0.59    ~spl8_5 | ~spl8_4 | spl8_13 | ~spl8_8),
% 1.64/0.59    inference(avatar_split_clause,[],[f176,f131,f179,f79,f83])).
% 1.64/0.59  fof(f176,plain,(
% 1.64/0.59    ( ! [X1] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X1)) = X1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_8),
% 1.64/0.59    inference(resolution,[],[f132,f54])).
% 1.64/0.59  fof(f174,plain,(
% 1.64/0.59    spl8_8 | spl8_7),
% 1.64/0.59    inference(avatar_split_clause,[],[f173,f128,f131])).
% 1.64/0.59  fof(f173,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 1.64/0.59    inference(global_subsumption,[],[f150])).
% 1.64/0.59  fof(f150,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.64/0.59    inference(superposition,[],[f146,f68])).
% 1.64/0.59  fof(f163,plain,(
% 1.64/0.59    spl8_10 | ~spl8_7 | ~spl8_9),
% 1.64/0.59    inference(avatar_split_clause,[],[f155,f142,f128,f161])).
% 1.64/0.59  fof(f155,plain,(
% 1.64/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl8_7 | ~spl8_9)),
% 1.64/0.59    inference(resolution,[],[f152,f129])).
% 1.64/0.59  fof(f144,plain,(
% 1.64/0.59    ~spl8_5 | ~spl8_4 | spl8_9 | ~spl8_3),
% 1.64/0.59    inference(avatar_split_clause,[],[f137,f75,f142,f79,f83])).
% 1.64/0.59  fof(f137,plain,(
% 1.64/0.59    ( ! [X6] : (r2_hidden(sK3(k1_xboole_0,X6),k1_xboole_0) | k2_relat_1(k1_xboole_0) = X6 | r2_hidden(sK2(k1_xboole_0,X6),X6) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_3),
% 1.64/0.59    inference(superposition,[],[f39,f76])).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f120,plain,(
% 1.64/0.59    ~spl8_5 | spl8_6 | ~spl8_3 | ~spl8_4),
% 1.64/0.59    inference(avatar_split_clause,[],[f115,f79,f75,f118,f83])).
% 1.64/0.59  fof(f115,plain,(
% 1.64/0.59    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl8_3 | ~spl8_4)),
% 1.64/0.59    inference(forward_demodulation,[],[f114,f76])).
% 1.64/0.59  fof(f114,plain,(
% 1.64/0.59    ( ! [X6] : (r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X6,k1_relat_1(k1_xboole_0))) ) | (~spl8_3 | ~spl8_4)),
% 1.64/0.59    inference(forward_demodulation,[],[f109,f76])).
% 1.64/0.59  fof(f109,plain,(
% 1.64/0.59    ( ! [X6] : (r2_hidden(sK4(k1_xboole_0,k1_funct_1(k1_xboole_0,X6)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X6,k1_relat_1(k1_xboole_0))) ) | ~spl8_4),
% 1.64/0.59    inference(resolution,[],[f103,f80])).
% 1.64/0.59  fof(f80,plain,(
% 1.64/0.59    v1_funct_1(k1_xboole_0) | ~spl8_4),
% 1.64/0.59    inference(avatar_component_clause,[],[f79])).
% 1.64/0.59  fof(f103,plain,(
% 1.64/0.59    ( ! [X2,X3] : (~v1_funct_1(X2) | r2_hidden(sK4(X2,k1_funct_1(X2,X3)),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2))) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f102])).
% 1.64/0.59  fof(f102,plain,(
% 1.64/0.59    ( ! [X2,X3] : (r2_hidden(sK4(X2,k1_funct_1(X2,X3)),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.64/0.59    inference(resolution,[],[f55,f53])).
% 1.64/0.59  fof(f85,plain,(
% 1.64/0.59    spl8_5),
% 1.64/0.59    inference(avatar_split_clause,[],[f73,f83])).
% 1.64/0.59  fof(f73,plain,(
% 1.64/0.59    v1_relat_1(k1_xboole_0)),
% 1.64/0.59    inference(superposition,[],[f44,f68])).
% 1.64/0.59  fof(f81,plain,(
% 1.64/0.59    spl8_4),
% 1.64/0.59    inference(avatar_split_clause,[],[f72,f79])).
% 1.64/0.59  fof(f72,plain,(
% 1.64/0.59    v1_funct_1(k1_xboole_0)),
% 1.64/0.59    inference(superposition,[],[f45,f68])).
% 1.64/0.59  fof(f77,plain,(
% 1.64/0.59    spl8_3),
% 1.64/0.59    inference(avatar_split_clause,[],[f71,f75])).
% 1.64/0.59  fof(f71,plain,(
% 1.64/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.64/0.59    inference(superposition,[],[f46,f68])).
% 1.64/0.59  fof(f62,plain,(
% 1.64/0.59    ~spl8_1 | spl8_2),
% 1.64/0.59    inference(avatar_split_clause,[],[f32,f60,f57])).
% 1.64/0.59  fof(f32,plain,(
% 1.64/0.59    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.64/0.59    inference(cnf_transformation,[],[f19])).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (6361)------------------------------
% 1.64/0.59  % (6361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (6361)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (6361)Memory used [KB]: 11257
% 1.64/0.59  % (6361)Time elapsed: 0.186 s
% 1.64/0.59  % (6361)------------------------------
% 1.64/0.59  % (6361)------------------------------
% 1.64/0.61  % (6341)Success in time 0.247 s
%------------------------------------------------------------------------------
