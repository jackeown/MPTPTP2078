%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 766 expanded)
%              Number of leaves         :   17 ( 260 expanded)
%              Depth                    :   18
%              Number of atoms          :  427 (4091 expanded)
%              Number of equality atoms :  144 (1567 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f243,f356])).

fof(f356,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f347,f286])).

fof(f286,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f193,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f193,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(unit_resulting_resolution,[],[f178,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f178,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f131,f173])).

fof(f173,plain,(
    ! [X0] : sK8(k2_relat_1(sK9(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f155,f169])).

fof(f169,plain,(
    ! [X0,X1] : k1_funct_1(sK9(sK1,X0),sK5(sK9(sK1,X1),sK8(k2_relat_1(sK9(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f160,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK9(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK9(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK9(X0,X1)) = X0
      & v1_funct_1(sK9(X0,X1))
      & v1_relat_1(sK9(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f18,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK9(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK9(X0,X1)) = X0
        & v1_funct_1(sK9(X0,X1))
        & v1_relat_1(sK9(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f160,plain,(
    ! [X0] : r2_hidden(sK5(sK9(sK1,X0),sK8(k2_relat_1(sK9(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f154,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_relat_1(sK9(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f154,plain,(
    ! [X0] : r2_hidden(sK5(sK9(sK1,X0),sK8(k2_relat_1(sK9(sK1,X0)),sK0)),k1_relat_1(sK9(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f130,f62])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f25,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f130,plain,(
    ! [X0] : r2_hidden(sK8(k2_relat_1(sK9(sK1,X0)),sK0),k2_relat_1(sK9(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f79,f53])).

fof(f79,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK9(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f37])).

fof(f37,plain,(
    ! [X2] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19])).

fof(f19,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f56,plain,(
    ! [X0,X1] : v1_funct_1(sK9(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(sK9(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,(
    ! [X0] : sK8(k2_relat_1(sK9(sK1,X0)),sK0) = k1_funct_1(sK9(sK1,X0),sK5(sK9(sK1,X0),sK8(k2_relat_1(sK9(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f130,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(sK8(k2_relat_1(sK9(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f79,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f347,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f285,f299])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f290,f285])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | r2_hidden(sK4(sK9(k1_xboole_0,X0),X1),k1_xboole_0)
        | r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f266,f65])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK9(k1_xboole_0,X0),X1),k1_xboole_0)
        | r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1)
        | ~ r1_tarski(X1,sK0) )
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f246,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1)
        | ~ r1_tarski(X1,sK0)
        | r2_hidden(sK4(sK9(sK1,X0),X1),sK1) )
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f137,f70])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK4(sK9(sK1,X0),X1),sK1)
      | r2_hidden(sK3(sK9(sK1,X0),X1),X1) ) ),
    inference(forward_demodulation,[],[f136,f57])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK4(sK9(sK1,X0),X1),k1_relat_1(sK9(sK1,X0)))
      | r2_hidden(sK3(sK9(sK1,X0),X1),X1) ) ),
    inference(subsumption_resolution,[],[f135,f55])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK4(sK9(sK1,X0),X1),k1_relat_1(sK9(sK1,X0)))
      | r2_hidden(sK3(sK9(sK1,X0),X1),X1)
      | ~ v1_relat_1(sK9(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f132,f56])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK4(sK9(sK1,X0),X1),k1_relat_1(sK9(sK1,X0)))
      | r2_hidden(sK3(sK9(sK1,X0),X1),X1)
      | ~ v1_funct_1(sK9(sK1,X0))
      | ~ v1_relat_1(sK9(sK1,X0)) ) ),
    inference(superposition,[],[f79,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f285,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f178,f65])).

fof(f243,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f225,f178])).

fof(f225,plain,
    ( r2_hidden(sK2(sK6(sK0),sK7(sK0)),sK0)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f74,f75,f77,f78,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK6(sK0) = X0
        | r2_hidden(sK2(sK6(sK0),X0),sK0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f89,f72])).

fof(f72,plain,
    ( v1_relat_1(sK6(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_relat_1(sK6(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

% (31222)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( sK6(X0) != sK7(X0)
        & k1_relat_1(sK7(X0)) = X0
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK7(X0))
        & v1_relat_1(sK7(X0))
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f30,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK6(X0) != X2
            & k1_relat_1(X2) = X0
            & k1_relat_1(sK6(X0)) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK6(X0) != X2
          & k1_relat_1(X2) = X0
          & k1_relat_1(sK6(X0)) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK6(X0) != sK7(X0)
        & k1_relat_1(sK7(X0)) = X0
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK7(X0))
        & v1_relat_1(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f66,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK6(sK0) = X0
        | r2_hidden(sK2(sK6(sK0),X0),sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK6(sK0)) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f80,f73])).

fof(f73,plain,
    ( v1_funct_1(sK6(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_funct_1(sK6(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK6(sK0) = X0
        | r2_hidden(sK2(sK6(sK0),X0),sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK6(sK0))
        | ~ v1_relat_1(sK6(sK0)) )
    | spl10_1 ),
    inference(superposition,[],[f38,f76])).

fof(f76,plain,
    ( sK0 = k1_relat_1(sK6(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f78,plain,
    ( sK6(sK0) != sK7(sK0)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | sK6(X0) != sK7(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,
    ( sK0 = k1_relat_1(sK7(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(sK7(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,
    ( v1_funct_1(sK7(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_funct_1(sK7(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,
    ( v1_relat_1(sK7(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_relat_1(sK7(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f36,f68,f64])).

fof(f36,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (31215)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (31231)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (31228)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (31219)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (31209)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31215)Refutation not found, incomplete strategy% (31215)------------------------------
% 0.21/0.51  % (31215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31232)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (31211)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (31223)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (31215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31215)Memory used [KB]: 10746
% 0.21/0.52  % (31215)Time elapsed: 0.095 s
% 0.21/0.52  % (31215)------------------------------
% 0.21/0.52  % (31215)------------------------------
% 0.21/0.53  % (31206)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31224)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (31206)Refutation not found, incomplete strategy% (31206)------------------------------
% 0.21/0.53  % (31206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31206)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31206)Memory used [KB]: 10618
% 0.21/0.53  % (31206)Time elapsed: 0.115 s
% 0.21/0.53  % (31206)------------------------------
% 0.21/0.53  % (31206)------------------------------
% 0.21/0.53  % (31217)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31221)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (31210)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (31207)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (31230)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (31205)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (31231)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f71,f243,f356])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    ~spl10_1 | ~spl10_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f355])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    $false | (~spl10_1 | ~spl10_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f347,f286])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl10_1),
% 0.21/0.54    inference(backward_demodulation,[],[f193,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl10_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl10_1 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f178,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK8(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f131,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0] : (sK8(k2_relat_1(sK9(sK1,X0)),sK0) = X0) )),
% 0.21/0.54    inference(backward_demodulation,[],[f155,f169])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_funct_1(sK9(sK1,X0),sK5(sK9(sK1,X1),sK8(k2_relat_1(sK9(sK1,X1)),sK0))) = X0) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f160,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (k1_funct_1(sK9(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X3] : (k1_funct_1(sK9(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK9(X0,X1)) = X0 & v1_funct_1(sK9(X0,X1)) & v1_relat_1(sK9(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f18,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK9(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK9(X0,X1)) = X0 & v1_funct_1(sK9(X0,X1)) & v1_relat_1(sK9(X0,X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK5(sK9(sK1,X0),sK8(k2_relat_1(sK9(sK1,X0)),sK0)),sK1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f154,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK9(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK5(sK9(sK1,X0),sK8(k2_relat_1(sK9(sK1,X0)),sK0)),k1_relat_1(sK9(sK1,X0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f55,f56,f130,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(rectify,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK8(k2_relat_1(sK9(sK1,X0)),sK0),k2_relat_1(sK9(sK1,X0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f79,f53])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK9(sK1,X0)),sK0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f55,f56,f57,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_1(sK9(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK9(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0] : (sK8(k2_relat_1(sK9(sK1,X0)),sK0) = k1_funct_1(sK9(sK1,X0),sK5(sK9(sK1,X0),sK8(k2_relat_1(sK9(sK1,X0)),sK0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f55,f56,f130,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK8(k2_relat_1(sK9(sK1,X0)),sK0),sK0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f79,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK8(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl10_1 | ~spl10_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f285,f299])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1)) ) | (~spl10_1 | ~spl10_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f290,f285])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r2_hidden(sK4(sK9(k1_xboole_0,X0),X1),k1_xboole_0) | r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1)) ) | (~spl10_1 | ~spl10_2)),
% 0.21/0.54    inference(backward_demodulation,[],[f266,f65])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(sK9(k1_xboole_0,X0),X1),k1_xboole_0) | r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1) | ~r1_tarski(X1,sK0)) ) | ~spl10_2),
% 0.21/0.54    inference(forward_demodulation,[],[f246,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl10_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl10_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(sK9(k1_xboole_0,X0),X1),X1) | ~r1_tarski(X1,sK0) | r2_hidden(sK4(sK9(sK1,X0),X1),sK1)) ) | ~spl10_2),
% 0.21/0.54    inference(backward_demodulation,[],[f137,f70])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK4(sK9(sK1,X0),X1),sK1) | r2_hidden(sK3(sK9(sK1,X0),X1),X1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f136,f57])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK4(sK9(sK1,X0),X1),k1_relat_1(sK9(sK1,X0))) | r2_hidden(sK3(sK9(sK1,X0),X1),X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f135,f55])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK4(sK9(sK1,X0),X1),k1_relat_1(sK9(sK1,X0))) | r2_hidden(sK3(sK9(sK1,X0),X1),X1) | ~v1_relat_1(sK9(sK1,X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f132,f56])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK4(sK9(sK1,X0),X1),k1_relat_1(sK9(sK1,X0))) | r2_hidden(sK3(sK9(sK1,X0),X1),X1) | ~v1_funct_1(sK9(sK1,X0)) | ~v1_relat_1(sK9(sK1,X0))) )),
% 0.21/0.54    inference(superposition,[],[f79,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r2_hidden(sK3(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl10_1),
% 0.21/0.54    inference(backward_demodulation,[],[f178,f65])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    spl10_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f242])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    $false | spl10_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f225,f178])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    r2_hidden(sK2(sK6(sK0),sK7(sK0)),sK0) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f74,f75,f77,f78,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | sK6(sK0) = X0 | r2_hidden(sK2(sK6(sK0),X0),sK0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | spl10_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f89,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    v1_relat_1(sK6(sK0)) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | v1_relat_1(sK6(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  % (31222)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ((sK6(X0) != sK7(X0) & k1_relat_1(sK7(X0)) = X0 & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0))) & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f30,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK6(X0) != X2 & k1_relat_1(X2) = X0 & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : (? [X2] : (sK6(X0) != X2 & k1_relat_1(X2) = X0 & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (sK6(X0) != sK7(X0) & k1_relat_1(sK7(X0)) = X0 & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK7(X0)) & v1_relat_1(sK7(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ? [X1] : (? [X2] : (X1 != X2 & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ? [X1] : (? [X2] : ((X1 != X2 & (k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | spl10_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) != sK0 | sK6(sK0) = X0 | r2_hidden(sK2(sK6(sK0),X0),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK6(sK0))) ) | spl10_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f80,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    v1_funct_1(sK6(sK0)) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | v1_funct_1(sK6(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) != sK0 | sK6(sK0) = X0 | r2_hidden(sK2(sK6(sK0),X0),sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK6(sK0)) | ~v1_relat_1(sK6(sK0))) ) | spl10_1),
% 0.21/0.54    inference(superposition,[],[f38,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK6(sK0)) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(sK6(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    sK6(sK0) != sK7(sK0) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | sK6(X0) != sK7(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK7(sK0)) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(sK7(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    v1_funct_1(sK7(sK0)) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | v1_funct_1(sK7(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    v1_relat_1(sK7(sK0)) | spl10_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f66,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | v1_relat_1(sK7(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~spl10_1 | spl10_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f68,f64])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31231)------------------------------
% 0.21/0.54  % (31231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31231)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31231)Memory used [KB]: 10874
% 0.21/0.54  % (31231)Time elapsed: 0.127 s
% 0.21/0.54  % (31231)------------------------------
% 0.21/0.54  % (31231)------------------------------
% 0.21/0.54  % (31222)Refutation not found, incomplete strategy% (31222)------------------------------
% 0.21/0.54  % (31222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31222)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31222)Memory used [KB]: 10746
% 0.21/0.54  % (31222)Time elapsed: 0.139 s
% 0.21/0.54  % (31222)------------------------------
% 0.21/0.54  % (31222)------------------------------
% 0.21/0.54  % (31233)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (31234)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (31226)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (31203)Success in time 0.185 s
%------------------------------------------------------------------------------
