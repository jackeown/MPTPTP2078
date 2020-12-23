%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 158 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  247 ( 678 expanded)
%              Number of equality atoms :   36 (  96 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f179,f268])).

fof(f268,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f29,f254])).

fof(f254,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f250,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f250,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = sK0
    | ~ spl5_3 ),
    inference(resolution,[],[f230,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = sK0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f228,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f228,plain,
    ( ! [X8,X7] :
        ( r2_hidden(sK4(sK0,X7,X8),X8)
        | sK0 = X8 )
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f207,f211])).

fof(f211,plain,
    ( ! [X9] : sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,X9))
    | ~ spl5_3 ),
    inference(resolution,[],[f205,f77])).

fof(f77,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_3
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f205,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK4(X3,X4,sK0),X3)
        | sK0 = k5_xboole_0(X3,k3_xboole_0(X3,X4)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f207,plain,
    ( ! [X8,X7] :
        ( r2_hidden(sK4(sK0,X7,X8),X8)
        | k5_xboole_0(sK0,k3_xboole_0(sK0,X7)) = X8 )
    | ~ spl5_3 ),
    inference(resolution,[],[f77,f49])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f179,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f29,f157])).

fof(f157,plain,
    ( k1_xboole_0 = sK0
    | spl5_4 ),
    inference(forward_demodulation,[],[f153,f32])).

fof(f153,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = sK0
    | spl5_4 ),
    inference(resolution,[],[f137,f31])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = sK0 )
    | spl5_4 ),
    inference(resolution,[],[f127,f35])).

fof(f127,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK4(sK0,X8,X9),X9)
        | sK0 = X9 )
    | spl5_4 ),
    inference(forward_demodulation,[],[f102,f106])).

fof(f106,plain,
    ( ! [X9] : sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,X9))
    | spl5_4 ),
    inference(resolution,[],[f100,f93])).

fof(f93,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl5_4 ),
    inference(resolution,[],[f80,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f80,plain,
    ( ~ r2_hidden(sK3(sK0),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK4(X4,X5,sK0),X4)
        | sK0 = k5_xboole_0(X4,k3_xboole_0(X4,X5)) )
    | spl5_4 ),
    inference(resolution,[],[f93,f49])).

fof(f102,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK4(sK0,X8,X9),X9)
        | k5_xboole_0(sK0,k3_xboole_0(sK0,X8)) = X9 )
    | spl5_4 ),
    inference(resolution,[],[f93,f49])).

fof(f81,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f74,f79,f76])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0),sK0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK3(sK0),sK0) ) ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X1] :
      ( r2_hidden(sK2(X1,sK0),sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f30,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(sK3(X2),sK0),X2)
      | ~ r2_hidden(sK3(X2),sK0)
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f56,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,sK0),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 17:44:34 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.52  % (2244)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (2256)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (2248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (2245)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (2232)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (2256)Refutation not found, incomplete strategy% (2256)------------------------------
% 0.20/0.53  % (2256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2256)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2256)Memory used [KB]: 10618
% 0.20/0.53  % (2256)Time elapsed: 0.066 s
% 0.20/0.53  % (2256)------------------------------
% 0.20/0.53  % (2256)------------------------------
% 0.20/0.53  % (2236)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (2236)Refutation not found, incomplete strategy% (2236)------------------------------
% 0.20/0.53  % (2236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2236)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2236)Memory used [KB]: 6140
% 0.20/0.53  % (2236)Time elapsed: 0.125 s
% 0.20/0.53  % (2236)------------------------------
% 0.20/0.53  % (2236)------------------------------
% 0.20/0.53  % (2242)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (2238)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (2240)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (2233)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (2251)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (2239)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (2244)Refutation not found, incomplete strategy% (2244)------------------------------
% 0.20/0.53  % (2244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2234)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2260)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (2257)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (2235)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (2249)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (2244)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2244)Memory used [KB]: 10618
% 0.20/0.54  % (2244)Time elapsed: 0.137 s
% 0.20/0.54  % (2244)------------------------------
% 0.20/0.54  % (2244)------------------------------
% 0.20/0.54  % (2262)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (2260)Refutation not found, incomplete strategy% (2260)------------------------------
% 0.20/0.54  % (2260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2260)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2260)Memory used [KB]: 10618
% 0.20/0.54  % (2260)Time elapsed: 0.139 s
% 0.20/0.54  % (2260)------------------------------
% 0.20/0.54  % (2260)------------------------------
% 0.20/0.54  % (2259)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (2259)Refutation not found, incomplete strategy% (2259)------------------------------
% 0.20/0.54  % (2259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (2250)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (2263)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (2246)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (2241)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (2234)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (2247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (2254)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (2261)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (2259)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2259)Memory used [KB]: 6140
% 0.20/0.55  % (2259)Time elapsed: 0.141 s
% 0.20/0.55  % (2259)------------------------------
% 0.20/0.55  % (2259)------------------------------
% 0.20/0.55  % (2258)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (2254)Refutation not found, incomplete strategy% (2254)------------------------------
% 0.20/0.55  % (2254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2254)Memory used [KB]: 10618
% 0.20/0.55  % (2254)Time elapsed: 0.150 s
% 0.20/0.55  % (2254)------------------------------
% 0.20/0.55  % (2254)------------------------------
% 0.20/0.55  % (2255)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (2252)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f277,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f81,f179,f268])).
% 0.20/0.56  fof(f268,plain,(
% 0.20/0.56    ~spl5_3),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f255])).
% 0.20/0.56  fof(f255,plain,(
% 0.20/0.56    $false | ~spl5_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f29,f254])).
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | ~spl5_3),
% 0.20/0.56    inference(forward_demodulation,[],[f250,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.56  fof(f250,plain,(
% 0.20/0.56    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = sK0) ) | ~spl5_3),
% 0.20/0.56    inference(resolution,[],[f230,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.56  fof(f230,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = sK0) ) | ~spl5_3),
% 0.20/0.56    inference(resolution,[],[f228,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.56  fof(f228,plain,(
% 0.20/0.56    ( ! [X8,X7] : (r2_hidden(sK4(sK0,X7,X8),X8) | sK0 = X8) ) | ~spl5_3),
% 0.20/0.56    inference(forward_demodulation,[],[f207,f211])).
% 0.20/0.56  fof(f211,plain,(
% 0.20/0.56    ( ! [X9] : (sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,X9))) ) | ~spl5_3),
% 0.20/0.56    inference(resolution,[],[f205,f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f76])).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    spl5_3 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.56  fof(f205,plain,(
% 0.20/0.56    ( ! [X4,X3] : (r2_hidden(sK4(X3,X4,sK0),X3) | sK0 = k5_xboole_0(X3,k3_xboole_0(X3,X4))) ) | ~spl5_3),
% 0.20/0.56    inference(resolution,[],[f77,f49])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.20/0.56    inference(definition_unfolding,[],[f44,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.56    inference(rectify,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.56    inference(flattening,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.56  fof(f207,plain,(
% 0.20/0.56    ( ! [X8,X7] : (r2_hidden(sK4(sK0,X7,X8),X8) | k5_xboole_0(sK0,k3_xboole_0(sK0,X7)) = X8) ) | ~spl5_3),
% 0.20/0.56    inference(resolution,[],[f77,f49])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    k1_xboole_0 != sK0),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.56    inference(negated_conjecture,[],[f8])).
% 0.20/0.56  fof(f8,conjecture,(
% 0.20/0.56    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.20/0.56  fof(f179,plain,(
% 0.20/0.56    spl5_4),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    $false | spl5_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f29,f157])).
% 0.20/0.56  fof(f157,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | spl5_4),
% 0.20/0.56    inference(forward_demodulation,[],[f153,f32])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = sK0) ) | spl5_4),
% 0.20/0.56    inference(resolution,[],[f137,f31])).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = sK0) ) | spl5_4),
% 0.20/0.56    inference(resolution,[],[f127,f35])).
% 0.20/0.56  fof(f127,plain,(
% 0.20/0.56    ( ! [X8,X9] : (r2_hidden(sK4(sK0,X8,X9),X9) | sK0 = X9) ) | spl5_4),
% 0.20/0.56    inference(forward_demodulation,[],[f102,f106])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ( ! [X9] : (sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,X9))) ) | spl5_4),
% 0.20/0.56    inference(resolution,[],[f100,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl5_4),
% 0.20/0.56    inference(resolution,[],[f80,f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ~r2_hidden(sK3(sK0),sK0) | spl5_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f79])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    spl5_4 <=> r2_hidden(sK3(sK0),sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5,sK0),X4) | sK0 = k5_xboole_0(X4,k3_xboole_0(X4,X5))) ) | spl5_4),
% 0.20/0.56    inference(resolution,[],[f93,f49])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    ( ! [X8,X9] : (r2_hidden(sK4(sK0,X8,X9),X9) | k5_xboole_0(sK0,k3_xboole_0(sK0,X8)) = X9) ) | spl5_4),
% 0.20/0.56    inference(resolution,[],[f93,f49])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    spl5_3 | ~spl5_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f74,f79,f76])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK3(sK0),sK0) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK3(sK0),sK0) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK3(sK0),sK0)) )),
% 0.20/0.56    inference(resolution,[],[f60,f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X1] : (r2_hidden(sK2(X1,sK0),sK0) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.56    inference(resolution,[],[f30,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ( ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X2,X3] : (~r2_hidden(sK2(sK3(X2),sK0),X2) | ~r2_hidden(sK3(X2),sK0) | ~r2_hidden(X3,X2)) )),
% 0.20/0.56    inference(resolution,[],[f56,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK2(X0,sK0),X0) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.56    inference(resolution,[],[f30,f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (2234)------------------------------
% 0.20/0.56  % (2234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (2234)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (2234)Memory used [KB]: 10746
% 0.20/0.56  % (2234)Time elapsed: 0.144 s
% 0.20/0.56  % (2234)------------------------------
% 0.20/0.56  % (2234)------------------------------
% 0.20/0.56  % (2226)Success in time 0.197 s
%------------------------------------------------------------------------------
