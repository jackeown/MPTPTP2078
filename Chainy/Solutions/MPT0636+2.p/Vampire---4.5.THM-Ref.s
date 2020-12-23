%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0636+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 4.66s
% Output     : Refutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 194 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  419 (1086 expanded)
%              Number of equality atoms :   57 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5065,f5824,f7186,f7204])).

fof(f7204,plain,
    ( ~ spl191_1
    | spl191_2 ),
    inference(avatar_contradiction_clause,[],[f7199])).

fof(f7199,plain,
    ( $false
    | ~ spl191_1
    | spl191_2 ),
    inference(unit_resulting_resolution,[],[f2246,f2247,f2269,f2317,f5060,f5063,f2936])).

fof(f2936,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1949])).

fof(f1949,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1948])).

fof(f1948,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1406])).

fof(f1406,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1405])).

fof(f1405,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f916])).

fof(f916,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f5063,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK7))
    | spl191_2 ),
    inference(avatar_component_clause,[],[f5062])).

fof(f5062,plain,
    ( spl191_2
  <=> r2_hidden(sK5,k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl191_2])])).

fof(f5060,plain,
    ( r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6))))
    | ~ spl191_1 ),
    inference(avatar_component_clause,[],[f5058])).

fof(f5058,plain,
    ( spl191_1
  <=> r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl191_1])])).

fof(f2317,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f899])).

fof(f899,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f2269,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f2247,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f1735])).

fof(f1735,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
      | ~ r2_hidden(sK5,k1_relat_1(sK7))
      | ~ r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) )
    & ( ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
        & r2_hidden(sK5,k1_relat_1(sK7)) )
      | r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) )
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f1733,f1734])).

fof(f1734,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
        | ~ r2_hidden(sK5,k1_relat_1(sK7))
        | ~ r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) )
      & ( ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
          & r2_hidden(sK5,k1_relat_1(sK7)) )
        | r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) )
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f1733,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1732])).

fof(f1732,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f947])).

fof(f947,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f946])).

fof(f946,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f927])).

fof(f927,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f926])).

fof(f926,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f2246,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f1735])).

fof(f7186,plain,
    ( ~ spl191_1
    | ~ spl191_2 ),
    inference(avatar_contradiction_clause,[],[f7185])).

fof(f7185,plain,
    ( $false
    | ~ spl191_1
    | ~ spl191_2 ),
    inference(subsumption_resolution,[],[f7180,f5846])).

fof(f5846,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ spl191_1
    | ~ spl191_2 ),
    inference(subsumption_resolution,[],[f5826,f5060])).

fof(f5826,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6))))
    | ~ spl191_2 ),
    inference(subsumption_resolution,[],[f2250,f5064])).

fof(f5064,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7))
    | ~ spl191_2 ),
    inference(avatar_component_clause,[],[f5062])).

fof(f2250,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(sK7))
    | ~ r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) ),
    inference(cnf_transformation,[],[f1735])).

fof(f7180,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ spl191_1 ),
    inference(resolution,[],[f5845,f5094])).

fof(f5094,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f3770,f2269])).

fof(f3770,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2699])).

fof(f2699,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1866])).

fof(f1866,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK66(X0,X1) != sK67(X0,X1)
              | ~ r2_hidden(sK66(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK66(X0,X1),sK67(X0,X1)),X1) )
            & ( ( sK66(X0,X1) = sK67(X0,X1)
                & r2_hidden(sK66(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK66(X0,X1),sK67(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK66,sK67])],[f1864,f1865])).

fof(f1865,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK66(X0,X1) != sK67(X0,X1)
          | ~ r2_hidden(sK66(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK66(X0,X1),sK67(X0,X1)),X1) )
        & ( ( sK66(X0,X1) = sK67(X0,X1)
            & r2_hidden(sK66(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK66(X0,X1),sK67(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1864,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1863])).

fof(f1863,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1862])).

fof(f1862,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1171])).

fof(f1171,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f5845,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK7,sK5),k1_funct_1(k6_relat_1(sK6),k1_funct_1(sK7,sK5))),k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(subsumption_resolution,[],[f5844,f2269])).

fof(f5844,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK7,sK5),k1_funct_1(k6_relat_1(sK6),k1_funct_1(sK7,sK5))),k6_relat_1(sK6))
    | ~ v1_relat_1(k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(subsumption_resolution,[],[f5839,f2317])).

fof(f5839,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK7,sK5),k1_funct_1(k6_relat_1(sK6),k1_funct_1(sK7,sK5))),k6_relat_1(sK6))
    | ~ v1_funct_1(k6_relat_1(sK6))
    | ~ v1_relat_1(k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(resolution,[],[f5836,f3758])).

fof(f3758,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2498])).

fof(f2498,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1803])).

fof(f1803,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1098])).

fof(f1098,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1097])).

fof(f1097,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f5836,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),k1_relat_1(k6_relat_1(sK6)))
    | ~ spl191_1 ),
    inference(subsumption_resolution,[],[f5835,f2269])).

fof(f5835,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),k1_relat_1(k6_relat_1(sK6)))
    | ~ v1_relat_1(k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(subsumption_resolution,[],[f5834,f2317])).

fof(f5834,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),k1_relat_1(k6_relat_1(sK6)))
    | ~ v1_funct_1(k6_relat_1(sK6))
    | ~ v1_relat_1(k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(subsumption_resolution,[],[f5833,f2246])).

fof(f5833,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),k1_relat_1(k6_relat_1(sK6)))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(k6_relat_1(sK6))
    | ~ v1_relat_1(k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(subsumption_resolution,[],[f5827,f2247])).

fof(f5827,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),k1_relat_1(k6_relat_1(sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(k6_relat_1(sK6))
    | ~ v1_relat_1(k6_relat_1(sK6))
    | ~ spl191_1 ),
    inference(resolution,[],[f5060,f2937])).

fof(f2937,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1949])).

fof(f5824,plain,
    ( spl191_1
    | ~ spl191_2 ),
    inference(avatar_contradiction_clause,[],[f5822])).

fof(f5822,plain,
    ( $false
    | spl191_1
    | ~ spl191_2 ),
    inference(unit_resulting_resolution,[],[f2246,f5066,f5153,f5815,f3484])).

fof(f3484,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f2161])).

fof(f2161,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f2160])).

fof(f2160,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1670])).

fof(f1670,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f867])).

fof(f867,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f5815,plain,
    ( ! [X40] : ~ r2_hidden(k4_tarski(sK5,X40),k5_relat_1(sK7,k6_relat_1(sK6)))
    | spl191_1 ),
    inference(resolution,[],[f3796,f5059])).

fof(f5059,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6))))
    | spl191_1 ),
    inference(avatar_component_clause,[],[f5058])).

fof(f3796,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f3029])).

fof(f3029,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2019])).

fof(f2019,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK118(X0,X1),X3),X0)
            | ~ r2_hidden(sK118(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK118(X0,X1),sK119(X0,X1)),X0)
            | r2_hidden(sK118(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK120(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK118,sK119,sK120])],[f2015,f2018,f2017,f2016])).

fof(f2016,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK118(X0,X1),X3),X0)
          | ~ r2_hidden(sK118(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK118(X0,X1),X4),X0)
          | r2_hidden(sK118(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2017,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK118(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK118(X0,X1),sK119(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2018,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK120(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2015,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f2014])).

fof(f2014,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f5153,plain,
    ( r2_hidden(k4_tarski(sK5,k1_funct_1(sK7,sK5)),sK7)
    | ~ spl191_2 ),
    inference(subsumption_resolution,[],[f5152,f2246])).

fof(f5152,plain,
    ( r2_hidden(k4_tarski(sK5,k1_funct_1(sK7,sK5)),sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl191_2 ),
    inference(subsumption_resolution,[],[f5147,f2247])).

fof(f5147,plain,
    ( r2_hidden(k4_tarski(sK5,k1_funct_1(sK7,sK5)),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl191_2 ),
    inference(resolution,[],[f3758,f5064])).

fof(f5066,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | spl191_1 ),
    inference(subsumption_resolution,[],[f2249,f5059])).

fof(f2249,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) ),
    inference(cnf_transformation,[],[f1735])).

fof(f5065,plain,
    ( spl191_1
    | spl191_2 ),
    inference(avatar_split_clause,[],[f2248,f5062,f5058])).

fof(f2248,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7))
    | r2_hidden(sK5,k1_relat_1(k5_relat_1(sK7,k6_relat_1(sK6)))) ),
    inference(cnf_transformation,[],[f1735])).
%------------------------------------------------------------------------------
