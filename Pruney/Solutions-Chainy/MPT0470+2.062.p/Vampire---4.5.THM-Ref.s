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
% DateTime   : Thu Dec  3 12:47:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 163 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  307 ( 579 expanded)
%              Number of equality atoms :   49 ( 125 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f82,f85,f103,f115,f124,f234,f238])).

fof(f238,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f209,f212])).

fof(f212,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_16
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f209,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f203,f56])).

fof(f56,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f203,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(resolution,[],[f200,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f200,plain,
    ( ! [X10,X9] : ~ r2_hidden(k4_tarski(X9,X10),k5_relat_1(k1_xboole_0,sK0))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(resolution,[],[f196,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f196,plain,
    ( ! [X10,X8,X9] :
        ( ~ v1_relat_1(X10)
        | ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(k1_xboole_0,X10)) )
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f114,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f114,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X10))
        | ~ v1_relat_1(X10) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_8
  <=> ! [X9,X8,X10] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X10))
        | ~ v1_relat_1(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f234,plain,
    ( ~ spl7_4
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl7_4
    | spl7_16 ),
    inference(subsumption_resolution,[],[f232,f80])).

fof(f80,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f232,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_16 ),
    inference(subsumption_resolution,[],[f230,f30])).

fof(f230,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl7_16 ),
    inference(resolution,[],[f213,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f213,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f124,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f122,f30])).

fof(f122,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f120,f80])).

fof(f120,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl7_5 ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_5
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f115,plain,
    ( ~ spl7_5
    | spl7_8
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f94,f76,f113,f100])).

fof(f76,plain,
    ( spl7_3
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f94,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X10))
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f89,plain,
    ( ! [X10,X9] : ~ r2_hidden(k4_tarski(X9,X10),k5_relat_1(sK0,k1_xboole_0))
    | ~ spl7_3 ),
    inference(resolution,[],[f77,f30])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f103,plain,
    ( ~ spl7_5
    | spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f91,f76,f58,f100])).

fof(f91,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f36])).

fof(f85,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f83,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_4 ),
    inference(resolution,[],[f81,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f81,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,
    ( spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f74,f79,f76])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f65,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_xboole_0(X3,k1_enumset1(k4_tarski(sK6(X2,X3,X0,X1),X1),k4_tarski(sK6(X2,X3,X0,X1),X1),k4_tarski(sK6(X2,X3,X0,X1),X1))) != X3
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) ) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f31,f58,f54])).

fof(f31,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (30889)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (30889)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (30907)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (30898)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f61,f82,f85,f103,f115,f124,f234,f238])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_16),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    $false | (spl7_1 | ~spl7_2 | ~spl7_8 | ~spl7_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f209,f212])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl7_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    spl7_16 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (spl7_1 | ~spl7_2 | ~spl7_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f203,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl7_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl7_2 | ~spl7_8)),
% 0.21/0.49    inference(resolution,[],[f200,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X9,X10),k5_relat_1(k1_xboole_0,sK0))) ) | (~spl7_2 | ~spl7_8)),
% 0.21/0.49    inference(resolution,[],[f196,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X10,X8,X9] : (~v1_relat_1(X10) | ~r2_hidden(k4_tarski(X8,X9),k5_relat_1(k1_xboole_0,X10))) ) | (~spl7_2 | ~spl7_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f114,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl7_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X10)) | ~v1_relat_1(X10)) ) | ~spl7_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl7_8 <=> ! [X9,X8,X10] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X10)) | ~v1_relat_1(X10))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~spl7_4 | spl7_16),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    $false | (~spl7_4 | spl7_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl7_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | spl7_16),
% 0.21/0.49    inference(subsumption_resolution,[],[f230,f30])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl7_16),
% 0.21/0.49    inference(resolution,[],[f213,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl7_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f211])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl7_4 | spl7_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    $false | (~spl7_4 | spl7_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f30])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | (~spl7_4 | spl7_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f80])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl7_5),
% 0.21/0.49    inference(resolution,[],[f102,f44])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl7_5 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~spl7_5 | spl7_8 | ~spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f94,f76,f113,f100])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl7_3 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X10)) | ~v1_relat_1(X10) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))) ) | ~spl7_3),
% 0.21/0.49    inference(resolution,[],[f89,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f44])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X9,X10),k5_relat_1(sK0,k1_xboole_0))) ) | ~spl7_3),
% 0.21/0.49    inference(resolution,[],[f77,f30])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0))) ) | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~spl7_5 | spl7_2 | ~spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f76,f58,f100])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl7_3),
% 0.21/0.49    inference(resolution,[],[f89,f36])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl7_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    $false | spl7_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | spl7_4),
% 0.21/0.49    inference(resolution,[],[f81,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl7_3 | ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f74,f79,f76])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(superposition,[],[f65,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k1_enumset1(k4_tarski(sK6(X2,X3,X0,X1),X1),k4_tarski(sK6(X2,X3,X0,X1),X1),k4_tarski(sK6(X2,X3,X0,X1),X1))) != X3 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))) )),
% 0.21/0.49    inference(resolution,[],[f64,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f45,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f44])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~spl7_1 | ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f58,f54])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30889)------------------------------
% 0.21/0.49  % (30889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30889)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30889)Memory used [KB]: 10874
% 0.21/0.49  % (30889)Time elapsed: 0.085 s
% 0.21/0.49  % (30889)------------------------------
% 0.21/0.49  % (30889)------------------------------
% 0.21/0.50  % (30883)Success in time 0.14 s
%------------------------------------------------------------------------------
