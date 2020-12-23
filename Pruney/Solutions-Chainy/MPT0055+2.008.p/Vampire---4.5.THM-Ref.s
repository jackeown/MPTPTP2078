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
% DateTime   : Thu Dec  3 12:30:05 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 149 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 729 expanded)
%              Number of equality atoms :   30 ( 106 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f308,f568,f610,f1865,f1872,f1876,f2626])).

fof(f2626,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f2625])).

fof(f2625,plain,
    ( $false
    | spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f2624,f131])).

fof(f131,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_9
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f2624,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f2610,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2610,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f323,f116])).

fof(f116,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_8
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f323,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) )
    | spl5_7 ),
    inference(resolution,[],[f111,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f111,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_7
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1876,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1873])).

fof(f1873,plain,
    ( $false
    | ~ spl5_12 ),
    inference(resolution,[],[f229,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f229,plain,
    ( ! [X0] : ~ r1_tarski(X0,k3_xboole_0(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_12
  <=> ! [X0] : ~ r1_tarski(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1872,plain,
    ( spl5_12
    | ~ spl5_18
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f603,f110,f367,f228])).

fof(f367,plain,
    ( spl5_18
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
        | ~ r1_tarski(X0,k3_xboole_0(sK0,sK1)) )
    | ~ spl5_7 ),
    inference(superposition,[],[f122,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f122,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))
    | ~ spl5_7 ),
    inference(resolution,[],[f112,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1865,plain,
    ( ~ spl5_7
    | spl5_8
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1864])).

fof(f1864,plain,
    ( $false
    | ~ spl5_7
    | spl5_8
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1863,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1863,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl5_7
    | spl5_8
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1857,f369])).

fof(f369,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f367])).

fof(f1857,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl5_7
    | spl5_8 ),
    inference(superposition,[],[f1032,f43])).

fof(f1032,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ spl5_7
    | spl5_8 ),
    inference(resolution,[],[f206,f112])).

fof(f206,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0)) )
    | spl5_8 ),
    inference(resolution,[],[f115,f58])).

fof(f115,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f610,plain,
    ( ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f602,f132])).

fof(f132,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f602,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl5_7 ),
    inference(superposition,[],[f122,f44])).

fof(f568,plain,
    ( ~ spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f567,f110,f130,f114])).

fof(f567,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f557,f35])).

fof(f35,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f557,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f112,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f308,plain,
    ( spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f137,f130,f110])).

fof(f137,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f117,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (9870)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (9870)Refutation not found, incomplete strategy% (9870)------------------------------
% 0.22/0.47  % (9870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9875)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (9859)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (9857)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (9860)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (9857)Refutation not found, incomplete strategy% (9857)------------------------------
% 0.22/0.48  % (9857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9857)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (9857)Memory used [KB]: 6140
% 0.22/0.48  % (9857)Time elapsed: 0.055 s
% 0.22/0.48  % (9857)------------------------------
% 0.22/0.48  % (9857)------------------------------
% 0.22/0.48  % (9870)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (9870)Memory used [KB]: 1663
% 0.22/0.48  % (9870)Time elapsed: 0.054 s
% 0.22/0.48  % (9860)Refutation not found, incomplete strategy% (9860)------------------------------
% 0.22/0.48  % (9860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9870)------------------------------
% 0.22/0.48  % (9870)------------------------------
% 0.22/0.48  % (9860)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (9860)Memory used [KB]: 10618
% 0.22/0.48  % (9860)Time elapsed: 0.073 s
% 0.22/0.48  % (9860)------------------------------
% 0.22/0.48  % (9860)------------------------------
% 0.22/0.48  % (9864)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (9867)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (9867)Refutation not found, incomplete strategy% (9867)------------------------------
% 0.22/0.49  % (9867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9867)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9867)Memory used [KB]: 6012
% 0.22/0.49  % (9867)Time elapsed: 0.073 s
% 0.22/0.49  % (9867)------------------------------
% 0.22/0.49  % (9867)------------------------------
% 0.22/0.49  % (9858)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (9858)Refutation not found, incomplete strategy% (9858)------------------------------
% 0.22/0.49  % (9858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9858)Memory used [KB]: 10618
% 0.22/0.49  % (9858)Time elapsed: 0.070 s
% 0.22/0.49  % (9858)------------------------------
% 0.22/0.49  % (9858)------------------------------
% 0.22/0.49  % (9872)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (9871)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (9872)Refutation not found, incomplete strategy% (9872)------------------------------
% 0.22/0.49  % (9872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9872)Memory used [KB]: 6140
% 0.22/0.49  % (9872)Time elapsed: 0.045 s
% 0.22/0.49  % (9872)------------------------------
% 0.22/0.49  % (9872)------------------------------
% 0.22/0.49  % (9862)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (9863)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (9876)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (9873)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (9861)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (9868)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (9868)Refutation not found, incomplete strategy% (9868)------------------------------
% 0.22/0.51  % (9868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9868)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9868)Memory used [KB]: 10618
% 0.22/0.51  % (9868)Time elapsed: 0.093 s
% 0.22/0.51  % (9868)------------------------------
% 0.22/0.51  % (9868)------------------------------
% 0.22/0.51  % (9869)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (9869)Refutation not found, incomplete strategy% (9869)------------------------------
% 0.22/0.51  % (9869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9869)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9869)Memory used [KB]: 6012
% 0.22/0.51  % (9869)Time elapsed: 0.001 s
% 0.22/0.51  % (9869)------------------------------
% 0.22/0.51  % (9869)------------------------------
% 0.22/0.51  % (9865)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (9877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (9877)Refutation not found, incomplete strategy% (9877)------------------------------
% 0.22/0.51  % (9877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9874)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (9866)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (9877)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (9877)Memory used [KB]: 10490
% 1.35/0.54  % (9877)Time elapsed: 0.113 s
% 1.35/0.54  % (9877)------------------------------
% 1.35/0.54  % (9877)------------------------------
% 1.62/0.59  % (9876)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f2628,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(avatar_sat_refutation,[],[f117,f308,f568,f610,f1865,f1872,f1876,f2626])).
% 1.62/0.59  fof(f2626,plain,(
% 1.62/0.59    spl5_7 | ~spl5_8 | spl5_9),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f2625])).
% 1.62/0.59  fof(f2625,plain,(
% 1.62/0.59    $false | (spl5_7 | ~spl5_8 | spl5_9)),
% 1.62/0.59    inference(subsumption_resolution,[],[f2624,f131])).
% 1.62/0.59  fof(f131,plain,(
% 1.62/0.59    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl5_9),
% 1.62/0.59    inference(avatar_component_clause,[],[f130])).
% 1.62/0.59  fof(f130,plain,(
% 1.62/0.59    spl5_9 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.62/0.59  fof(f2624,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl5_7 | ~spl5_8)),
% 1.62/0.59    inference(forward_demodulation,[],[f2610,f44])).
% 1.62/0.59  fof(f44,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f14])).
% 1.62/0.59  fof(f14,axiom,(
% 1.62/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.62/0.59  fof(f2610,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl5_7 | ~spl5_8)),
% 1.62/0.59    inference(resolution,[],[f323,f116])).
% 1.62/0.59  fof(f116,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_8),
% 1.62/0.59    inference(avatar_component_clause,[],[f114])).
% 1.62/0.59  fof(f114,plain,(
% 1.62/0.59    spl5_8 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.62/0.59  fof(f323,plain,(
% 1.62/0.59    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | spl5_7),
% 1.62/0.59    inference(resolution,[],[f111,f58])).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.62/0.59    inference(equality_resolution,[],[f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.62/0.59  fof(f29,plain,(
% 1.62/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(rectify,[],[f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(flattening,[],[f26])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(nnf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.62/0.59  fof(f111,plain,(
% 1.62/0.59    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl5_7),
% 1.62/0.59    inference(avatar_component_clause,[],[f110])).
% 1.62/0.59  fof(f110,plain,(
% 1.62/0.59    spl5_7 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.62/0.59  fof(f1876,plain,(
% 1.62/0.59    ~spl5_12),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f1873])).
% 1.62/0.59  fof(f1873,plain,(
% 1.62/0.59    $false | ~spl5_12),
% 1.62/0.59    inference(resolution,[],[f229,f51])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,axiom,(
% 1.62/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.62/0.59  fof(f229,plain,(
% 1.62/0.59    ( ! [X0] : (~r1_tarski(X0,k3_xboole_0(sK0,sK1))) ) | ~spl5_12),
% 1.62/0.59    inference(avatar_component_clause,[],[f228])).
% 1.62/0.59  fof(f228,plain,(
% 1.62/0.59    spl5_12 <=> ! [X0] : ~r1_tarski(X0,k3_xboole_0(sK0,sK1))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.62/0.59  fof(f1872,plain,(
% 1.62/0.59    spl5_12 | ~spl5_18 | ~spl5_7),
% 1.62/0.59    inference(avatar_split_clause,[],[f603,f110,f367,f228])).
% 1.62/0.59  fof(f367,plain,(
% 1.62/0.59    spl5_18 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.62/0.59  fof(f603,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~r1_tarski(X0,k3_xboole_0(sK0,sK1))) ) | ~spl5_7),
% 1.62/0.59    inference(superposition,[],[f122,f43])).
% 1.62/0.59  fof(f43,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.62/0.59    inference(unused_predicate_definition_removal,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.62/0.59  fof(f122,plain,(
% 1.62/0.59    ( ! [X2] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))) ) | ~spl5_7),
% 1.62/0.59    inference(resolution,[],[f112,f59])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.62/0.59    inference(equality_resolution,[],[f37])).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f112,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl5_7),
% 1.62/0.59    inference(avatar_component_clause,[],[f110])).
% 1.62/0.59  fof(f1865,plain,(
% 1.62/0.59    ~spl5_7 | spl5_8 | spl5_18),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f1864])).
% 1.62/0.59  fof(f1864,plain,(
% 1.62/0.59    $false | (~spl5_7 | spl5_8 | spl5_18)),
% 1.62/0.59    inference(subsumption_resolution,[],[f1863,f54])).
% 1.62/0.59  fof(f54,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.62/0.59  fof(f1863,plain,(
% 1.62/0.59    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl5_7 | spl5_8 | spl5_18)),
% 1.62/0.59    inference(subsumption_resolution,[],[f1857,f369])).
% 1.62/0.59  fof(f369,plain,(
% 1.62/0.59    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | spl5_18),
% 1.62/0.59    inference(avatar_component_clause,[],[f367])).
% 1.62/0.59  fof(f1857,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl5_7 | spl5_8)),
% 1.62/0.59    inference(superposition,[],[f1032,f43])).
% 1.62/0.59  fof(f1032,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl5_7 | spl5_8)),
% 1.62/0.59    inference(resolution,[],[f206,f112])).
% 1.62/0.59  fof(f206,plain,(
% 1.62/0.59    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))) ) | spl5_8),
% 1.62/0.59    inference(resolution,[],[f115,f58])).
% 1.62/0.59  fof(f115,plain,(
% 1.62/0.59    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl5_8),
% 1.62/0.59    inference(avatar_component_clause,[],[f114])).
% 1.62/0.59  fof(f610,plain,(
% 1.62/0.59    ~spl5_7 | ~spl5_9),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f609])).
% 1.62/0.59  fof(f609,plain,(
% 1.62/0.59    $false | (~spl5_7 | ~spl5_9)),
% 1.62/0.59    inference(subsumption_resolution,[],[f602,f132])).
% 1.62/0.59  fof(f132,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl5_9),
% 1.62/0.59    inference(avatar_component_clause,[],[f130])).
% 1.62/0.59  fof(f602,plain,(
% 1.62/0.59    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl5_7),
% 1.62/0.59    inference(superposition,[],[f122,f44])).
% 1.62/0.59  fof(f568,plain,(
% 1.62/0.59    ~spl5_8 | spl5_9 | ~spl5_7),
% 1.62/0.59    inference(avatar_split_clause,[],[f567,f110,f130,f114])).
% 1.62/0.59  fof(f567,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_7),
% 1.62/0.59    inference(subsumption_resolution,[],[f557,f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.62/0.59    inference(cnf_transformation,[],[f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f16])).
% 1.62/0.59  fof(f16,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.62/0.59    inference(negated_conjecture,[],[f15])).
% 1.62/0.59  fof(f15,conjecture,(
% 1.62/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.62/0.59  fof(f557,plain,(
% 1.62/0.59    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_7),
% 1.62/0.59    inference(resolution,[],[f112,f41])).
% 1.62/0.59  fof(f41,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f308,plain,(
% 1.62/0.59    spl5_7 | ~spl5_9),
% 1.62/0.59    inference(avatar_split_clause,[],[f137,f130,f110])).
% 1.62/0.59  fof(f137,plain,(
% 1.62/0.59    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.62/0.59    inference(equality_resolution,[],[f67])).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 1.62/0.59    inference(superposition,[],[f35,f40])).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f117,plain,(
% 1.62/0.59    spl5_7 | spl5_8),
% 1.62/0.59    inference(avatar_split_clause,[],[f108,f114,f110])).
% 1.62/0.59  fof(f108,plain,(
% 1.62/0.59    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.62/0.59    inference(equality_resolution,[],[f66])).
% 1.62/0.59  fof(f66,plain,(
% 1.62/0.59    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 1.62/0.59    inference(superposition,[],[f35,f39])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (9876)------------------------------
% 1.62/0.59  % (9876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (9876)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (9876)Memory used [KB]: 7036
% 1.62/0.59  % (9876)Time elapsed: 0.172 s
% 1.62/0.59  % (9876)------------------------------
% 1.62/0.59  % (9876)------------------------------
% 1.62/0.59  % (9856)Success in time 0.219 s
%------------------------------------------------------------------------------
