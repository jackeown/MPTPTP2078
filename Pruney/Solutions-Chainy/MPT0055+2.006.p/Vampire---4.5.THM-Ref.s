%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:05 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
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
fof(f2637,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f308,f568,f610,f1923,f1930,f1934,f2635])).

fof(f2635,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f2634])).

fof(f2634,plain,
    ( $false
    | spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f2633,f131])).

fof(f131,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_9
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f2633,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f2619,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2619,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f111,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_7
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1934,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1931])).

fof(f1931,plain,
    ( $false
    | ~ spl5_12 ),
    inference(resolution,[],[f229,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f229,plain,
    ( ! [X0] : ~ r1_tarski(X0,k3_xboole_0(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_12
  <=> ! [X0] : ~ r1_tarski(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1930,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

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

fof(f1923,plain,
    ( ~ spl5_7
    | spl5_8
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1922])).

fof(f1922,plain,
    ( $false
    | ~ spl5_7
    | spl5_8
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1921,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1921,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl5_7
    | spl5_8
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1915,f369])).

fof(f369,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f367])).

fof(f1915,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl5_7
    | spl5_8 ),
    inference(superposition,[],[f1040,f43])).

fof(f1040,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:52:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.45  % (1981)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (1976)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (1964)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (1976)Refutation not found, incomplete strategy% (1976)------------------------------
% 0.21/0.47  % (1976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (1976)Memory used [KB]: 1663
% 0.21/0.47  % (1976)Time elapsed: 0.004 s
% 0.21/0.47  % (1976)------------------------------
% 0.21/0.47  % (1976)------------------------------
% 0.21/0.47  % (1969)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (1983)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1983)Refutation not found, incomplete strategy% (1983)------------------------------
% 0.21/0.48  % (1983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1983)Memory used [KB]: 10490
% 0.21/0.48  % (1983)Time elapsed: 0.062 s
% 0.21/0.48  % (1983)------------------------------
% 0.21/0.48  % (1983)------------------------------
% 0.21/0.48  % (1964)Refutation not found, incomplete strategy% (1964)------------------------------
% 0.21/0.48  % (1964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1964)Memory used [KB]: 10618
% 0.21/0.48  % (1964)Time elapsed: 0.060 s
% 0.21/0.48  % (1964)------------------------------
% 0.21/0.48  % (1964)------------------------------
% 0.21/0.48  % (1974)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (1968)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1974)Refutation not found, incomplete strategy% (1974)------------------------------
% 0.21/0.49  % (1974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1974)Memory used [KB]: 10618
% 0.21/0.49  % (1974)Time elapsed: 0.069 s
% 0.21/0.49  % (1974)------------------------------
% 0.21/0.49  % (1974)------------------------------
% 0.21/0.49  % (1973)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (1966)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (1973)Refutation not found, incomplete strategy% (1973)------------------------------
% 0.21/0.49  % (1973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1973)Memory used [KB]: 6012
% 0.21/0.49  % (1973)Time elapsed: 0.082 s
% 0.21/0.49  % (1973)------------------------------
% 0.21/0.49  % (1973)------------------------------
% 0.21/0.49  % (1966)Refutation not found, incomplete strategy% (1966)------------------------------
% 0.21/0.49  % (1966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1966)Memory used [KB]: 10618
% 0.21/0.49  % (1966)Time elapsed: 0.074 s
% 0.21/0.49  % (1966)------------------------------
% 0.21/0.49  % (1966)------------------------------
% 0.21/0.49  % (1967)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (1975)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (1965)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (1975)Refutation not found, incomplete strategy% (1975)------------------------------
% 0.21/0.50  % (1975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1975)Memory used [KB]: 6012
% 0.21/0.50  % (1975)Time elapsed: 0.001 s
% 0.21/0.50  % (1975)------------------------------
% 0.21/0.50  % (1975)------------------------------
% 0.21/0.50  % (1979)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (1980)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (1982)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (1978)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (1978)Refutation not found, incomplete strategy% (1978)------------------------------
% 0.21/0.51  % (1978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1978)Memory used [KB]: 6140
% 0.21/0.51  % (1978)Time elapsed: 0.099 s
% 0.21/0.51  % (1978)------------------------------
% 0.21/0.51  % (1978)------------------------------
% 0.21/0.51  % (1972)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (1971)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (1977)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (1963)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (1963)Refutation not found, incomplete strategy% (1963)------------------------------
% 0.21/0.52  % (1963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1963)Memory used [KB]: 6140
% 0.21/0.52  % (1963)Time elapsed: 0.092 s
% 0.21/0.52  % (1963)------------------------------
% 0.21/0.52  % (1963)------------------------------
% 0.21/0.53  % (1970)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.64/0.61  % (1982)Refutation found. Thanks to Tanya!
% 1.64/0.61  % SZS status Theorem for theBenchmark
% 1.64/0.61  % SZS output start Proof for theBenchmark
% 1.64/0.61  fof(f2637,plain,(
% 1.64/0.61    $false),
% 1.64/0.61    inference(avatar_sat_refutation,[],[f117,f308,f568,f610,f1923,f1930,f1934,f2635])).
% 1.64/0.61  fof(f2635,plain,(
% 1.64/0.61    spl5_7 | ~spl5_8 | spl5_9),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f2634])).
% 1.64/0.61  fof(f2634,plain,(
% 1.64/0.61    $false | (spl5_7 | ~spl5_8 | spl5_9)),
% 1.64/0.61    inference(subsumption_resolution,[],[f2633,f131])).
% 1.64/0.61  fof(f131,plain,(
% 1.64/0.61    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl5_9),
% 1.64/0.61    inference(avatar_component_clause,[],[f130])).
% 1.64/0.61  fof(f130,plain,(
% 1.64/0.61    spl5_9 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.64/0.61  fof(f2633,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl5_7 | ~spl5_8)),
% 1.64/0.61    inference(forward_demodulation,[],[f2619,f44])).
% 1.64/0.61  fof(f44,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f14])).
% 1.64/0.61  fof(f14,axiom,(
% 1.64/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.64/0.61  fof(f2619,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl5_7 | ~spl5_8)),
% 1.64/0.61    inference(resolution,[],[f323,f116])).
% 1.64/0.61  fof(f116,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_8),
% 1.64/0.61    inference(avatar_component_clause,[],[f114])).
% 1.64/0.61  fof(f114,plain,(
% 1.64/0.61    spl5_8 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.64/0.61  fof(f323,plain,(
% 1.64/0.61    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | spl5_7),
% 1.64/0.61    inference(resolution,[],[f111,f58])).
% 1.64/0.61  fof(f58,plain,(
% 1.64/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.64/0.61    inference(equality_resolution,[],[f38])).
% 1.64/0.61  fof(f38,plain,(
% 1.64/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.61    inference(cnf_transformation,[],[f30])).
% 1.64/0.61  fof(f30,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.64/0.61  fof(f29,plain,(
% 1.64/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f28,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(rectify,[],[f27])).
% 1.64/0.61  fof(f27,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(flattening,[],[f26])).
% 1.64/0.61  fof(f26,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.64/0.61    inference(nnf_transformation,[],[f3])).
% 1.64/0.61  fof(f3,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.64/0.61  fof(f111,plain,(
% 1.64/0.61    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl5_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f110])).
% 1.64/0.61  fof(f110,plain,(
% 1.64/0.61    spl5_7 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.64/0.61  fof(f1934,plain,(
% 1.64/0.61    ~spl5_12),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f1931])).
% 1.64/0.61  fof(f1931,plain,(
% 1.64/0.61    $false | ~spl5_12),
% 1.64/0.61    inference(resolution,[],[f229,f51])).
% 1.64/0.61  fof(f51,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f10])).
% 1.64/0.61  fof(f10,axiom,(
% 1.64/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.64/0.61  fof(f229,plain,(
% 1.64/0.61    ( ! [X0] : (~r1_tarski(X0,k3_xboole_0(sK0,sK1))) ) | ~spl5_12),
% 1.64/0.61    inference(avatar_component_clause,[],[f228])).
% 1.64/0.61  fof(f228,plain,(
% 1.64/0.61    spl5_12 <=> ! [X0] : ~r1_tarski(X0,k3_xboole_0(sK0,sK1))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.64/0.61  fof(f1930,plain,(
% 1.64/0.61    spl5_12 | ~spl5_18 | ~spl5_7),
% 1.64/0.61    inference(avatar_split_clause,[],[f603,f110,f367,f228])).
% 1.64/0.61  fof(f367,plain,(
% 1.64/0.61    spl5_18 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.64/0.61  fof(f603,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~r1_tarski(X0,k3_xboole_0(sK0,sK1))) ) | ~spl5_7),
% 1.64/0.61    inference(superposition,[],[f122,f43])).
% 1.64/0.61  fof(f43,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f21,plain,(
% 1.64/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.64/0.61    inference(ennf_transformation,[],[f19])).
% 1.64/0.61  fof(f19,plain,(
% 1.64/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.64/0.61    inference(unused_predicate_definition_removal,[],[f6])).
% 1.64/0.61  fof(f6,axiom,(
% 1.64/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.64/0.61  fof(f122,plain,(
% 1.64/0.61    ( ! [X2] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))) ) | ~spl5_7),
% 1.64/0.61    inference(resolution,[],[f112,f59])).
% 1.64/0.61  fof(f59,plain,(
% 1.64/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.64/0.61    inference(equality_resolution,[],[f37])).
% 1.64/0.61  fof(f37,plain,(
% 1.64/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.61    inference(cnf_transformation,[],[f30])).
% 1.64/0.61  fof(f112,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl5_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f110])).
% 1.64/0.61  fof(f1923,plain,(
% 1.64/0.61    ~spl5_7 | spl5_8 | spl5_18),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f1922])).
% 1.64/0.61  fof(f1922,plain,(
% 1.64/0.61    $false | (~spl5_7 | spl5_8 | spl5_18)),
% 1.64/0.61    inference(subsumption_resolution,[],[f1921,f54])).
% 1.64/0.61  fof(f54,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f7])).
% 1.64/0.61  fof(f7,axiom,(
% 1.64/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.64/0.61  fof(f1921,plain,(
% 1.64/0.61    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl5_7 | spl5_8 | spl5_18)),
% 1.64/0.61    inference(subsumption_resolution,[],[f1915,f369])).
% 1.64/0.61  fof(f369,plain,(
% 1.64/0.61    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | spl5_18),
% 1.64/0.61    inference(avatar_component_clause,[],[f367])).
% 1.64/0.61  fof(f1915,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl5_7 | spl5_8)),
% 1.64/0.61    inference(superposition,[],[f1040,f43])).
% 1.64/0.61  fof(f1040,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl5_7 | spl5_8)),
% 1.64/0.61    inference(resolution,[],[f206,f112])).
% 1.64/0.61  fof(f206,plain,(
% 1.64/0.61    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))) ) | spl5_8),
% 1.64/0.61    inference(resolution,[],[f115,f58])).
% 1.64/0.61  fof(f115,plain,(
% 1.64/0.61    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl5_8),
% 1.64/0.61    inference(avatar_component_clause,[],[f114])).
% 1.64/0.61  fof(f610,plain,(
% 1.64/0.61    ~spl5_7 | ~spl5_9),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f609])).
% 1.64/0.61  fof(f609,plain,(
% 1.64/0.61    $false | (~spl5_7 | ~spl5_9)),
% 1.64/0.61    inference(subsumption_resolution,[],[f602,f132])).
% 1.64/0.61  fof(f132,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl5_9),
% 1.64/0.61    inference(avatar_component_clause,[],[f130])).
% 1.64/0.61  fof(f602,plain,(
% 1.64/0.61    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl5_7),
% 1.64/0.61    inference(superposition,[],[f122,f44])).
% 1.64/0.61  fof(f568,plain,(
% 1.64/0.61    ~spl5_8 | spl5_9 | ~spl5_7),
% 1.64/0.61    inference(avatar_split_clause,[],[f567,f110,f130,f114])).
% 1.64/0.61  fof(f567,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_7),
% 1.64/0.61    inference(subsumption_resolution,[],[f557,f35])).
% 1.64/0.61  fof(f35,plain,(
% 1.64/0.61    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.64/0.61    inference(cnf_transformation,[],[f25])).
% 1.64/0.61  fof(f25,plain,(
% 1.64/0.61    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).
% 1.64/0.61  fof(f24,plain,(
% 1.64/0.61    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f20,plain,(
% 1.64/0.61    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.61    inference(ennf_transformation,[],[f16])).
% 1.64/0.61  fof(f16,negated_conjecture,(
% 1.64/0.61    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.61    inference(negated_conjecture,[],[f15])).
% 1.64/0.61  fof(f15,conjecture,(
% 1.64/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.64/0.61  fof(f557,plain,(
% 1.64/0.61    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_7),
% 1.64/0.61    inference(resolution,[],[f112,f41])).
% 1.64/0.61  fof(f41,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f30])).
% 1.64/0.61  fof(f308,plain,(
% 1.64/0.61    spl5_7 | ~spl5_9),
% 1.64/0.61    inference(avatar_split_clause,[],[f137,f130,f110])).
% 1.64/0.61  fof(f137,plain,(
% 1.64/0.61    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.64/0.61    inference(equality_resolution,[],[f67])).
% 1.64/0.61  fof(f67,plain,(
% 1.64/0.61    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 1.64/0.61    inference(superposition,[],[f35,f40])).
% 1.64/0.61  fof(f40,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f30])).
% 1.64/0.61  fof(f117,plain,(
% 1.64/0.61    spl5_7 | spl5_8),
% 1.64/0.61    inference(avatar_split_clause,[],[f108,f114,f110])).
% 1.64/0.61  fof(f108,plain,(
% 1.64/0.61    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.64/0.61    inference(equality_resolution,[],[f66])).
% 1.64/0.61  fof(f66,plain,(
% 1.64/0.61    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 1.64/0.61    inference(superposition,[],[f35,f39])).
% 1.64/0.61  fof(f39,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f30])).
% 1.64/0.61  % SZS output end Proof for theBenchmark
% 1.64/0.61  % (1982)------------------------------
% 1.64/0.61  % (1982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (1982)Termination reason: Refutation
% 1.64/0.61  
% 1.64/0.61  % (1982)Memory used [KB]: 7036
% 1.64/0.61  % (1982)Time elapsed: 0.192 s
% 1.64/0.61  % (1982)------------------------------
% 1.64/0.61  % (1982)------------------------------
% 1.64/0.61  % (1962)Success in time 0.251 s
%------------------------------------------------------------------------------
