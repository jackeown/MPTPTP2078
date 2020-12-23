%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:21 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 212 expanded)
%              Number of leaves         :   10 (  53 expanded)
%              Depth                    :   19
%              Number of atoms          :  433 (1168 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f65,f66,f250,f276,f311])).

fof(f311,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f309,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f309,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f308,f43])).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f308,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f301,f297])).

fof(f297,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f295,f42])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))
        | ~ v1_relat_1(k6_relat_1(sK1)) )
    | spl5_3 ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK3(X0,X1) != sK4(X0,X1)
              | ~ r2_hidden(sK3(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( ( sK3(X0,X1) = sK4(X0,X1)
                & r2_hidden(sK3(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK3(X0,X1) != sK4(X0,X1)
          | ~ r2_hidden(sK3(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( ( sK3(X0,X1) = sK4(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f63,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f301,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))),k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f280,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f280,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f279,f42])).

fof(f279,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f278,f43])).

fof(f278,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f277,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f277,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f264,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f264,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f54,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f276,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f274,f42])).

fof(f274,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f273,f43])).

fof(f273,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f272,f28])).

fof(f272,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f271,f29])).

fof(f271,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f263,f59])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f263,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f250,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f248,f42])).

fof(f248,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f241,f62])).

fof(f62,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f241,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f173,f48])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f172,f42])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))
        | ~ v1_relat_1(k6_relat_1(sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f165,f43])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))
        | ~ v1_funct_1(k6_relat_1(sK1))
        | ~ v1_relat_1(k6_relat_1(sK1)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f122,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f122,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f121,f42])).

fof(f121,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f120,f43])).

fof(f120,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f119,f28])).

fof(f119,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f118,f29])).

fof(f118,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f111,f58])).

fof(f58,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f111,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_1 ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f66,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f57,f53])).

fof(f30,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f31,f61,f53])).

fof(f31,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f61,f57,f53])).

fof(f32,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:11:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (21793)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (21780)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (21784)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (21775)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.38/0.56  % (21788)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.38/0.56  % (21778)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.56  % (21792)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.38/0.56  % (21783)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.38/0.57  % (21776)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.38/0.57  % (21776)Refutation not found, incomplete strategy% (21776)------------------------------
% 1.38/0.57  % (21776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (21776)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (21776)Memory used [KB]: 1663
% 1.38/0.57  % (21776)Time elapsed: 0.142 s
% 1.38/0.57  % (21776)------------------------------
% 1.38/0.57  % (21776)------------------------------
% 1.38/0.57  % (21780)Refutation found. Thanks to Tanya!
% 1.38/0.57  % SZS status Theorem for theBenchmark
% 1.38/0.57  % SZS output start Proof for theBenchmark
% 1.38/0.57  fof(f318,plain,(
% 1.38/0.57    $false),
% 1.38/0.57    inference(avatar_sat_refutation,[],[f64,f65,f66,f250,f276,f311])).
% 1.38/0.57  fof(f311,plain,(
% 1.38/0.57    ~spl5_1 | spl5_3),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f310])).
% 1.38/0.57  fof(f310,plain,(
% 1.38/0.57    $false | (~spl5_1 | spl5_3)),
% 1.38/0.57    inference(subsumption_resolution,[],[f309,f42])).
% 1.38/0.57  fof(f42,plain,(
% 1.38/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f3])).
% 1.38/0.57  fof(f3,axiom,(
% 1.38/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.38/0.57  fof(f309,plain,(
% 1.38/0.57    ~v1_relat_1(k6_relat_1(sK1)) | (~spl5_1 | spl5_3)),
% 1.38/0.57    inference(subsumption_resolution,[],[f308,f43])).
% 1.38/0.57  fof(f43,plain,(
% 1.38/0.57    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f3])).
% 1.38/0.57  fof(f308,plain,(
% 1.38/0.57    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (~spl5_1 | spl5_3)),
% 1.38/0.57    inference(subsumption_resolution,[],[f301,f297])).
% 1.38/0.57  fof(f297,plain,(
% 1.38/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))) ) | spl5_3),
% 1.38/0.57    inference(subsumption_resolution,[],[f295,f42])).
% 1.38/0.57  fof(f295,plain,(
% 1.38/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))) ) | spl5_3),
% 1.38/0.57    inference(resolution,[],[f63,f50])).
% 1.38/0.57  fof(f50,plain,(
% 1.38/0.57    ( ! [X4,X0,X5] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.57    inference(equality_resolution,[],[f36])).
% 1.38/0.57  fof(f36,plain,(
% 1.38/0.57    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f25])).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK3(X0,X1) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & ((sK3(X0,X1) = sK4(X0,X1) & r2_hidden(sK3(X0,X1),X0)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).
% 1.38/0.57  fof(f24,plain,(
% 1.38/0.57    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK3(X0,X1) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & ((sK3(X0,X1) = sK4(X0,X1) & r2_hidden(sK3(X0,X1),X0)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1))))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f23,plain,(
% 1.38/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(rectify,[],[f22])).
% 1.38/0.57  fof(f22,plain,(
% 1.38/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(flattening,[],[f21])).
% 1.38/0.57  fof(f21,plain,(
% 1.38/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(nnf_transformation,[],[f12])).
% 1.38/0.57  fof(f12,plain,(
% 1.38/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f1])).
% 1.38/0.57  fof(f1,axiom,(
% 1.38/0.57    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 1.38/0.57  fof(f63,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl5_3),
% 1.38/0.57    inference(avatar_component_clause,[],[f61])).
% 1.38/0.57  fof(f61,plain,(
% 1.38/0.57    spl5_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.38/0.57  fof(f301,plain,(
% 1.38/0.57    r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))),k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl5_1),
% 1.38/0.57    inference(resolution,[],[f280,f51])).
% 1.38/0.57  fof(f51,plain,(
% 1.38/0.57    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.57    inference(equality_resolution,[],[f46])).
% 1.38/0.57  fof(f46,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f27])).
% 1.38/0.57  fof(f27,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.57    inference(flattening,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.57    inference(nnf_transformation,[],[f14])).
% 1.38/0.57  fof(f14,plain,(
% 1.38/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.57    inference(flattening,[],[f13])).
% 1.38/0.57  fof(f13,plain,(
% 1.38/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.38/0.57    inference(ennf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.38/0.57  fof(f280,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~spl5_1),
% 1.38/0.57    inference(subsumption_resolution,[],[f279,f42])).
% 1.38/0.57  fof(f279,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl5_1),
% 1.38/0.57    inference(subsumption_resolution,[],[f278,f43])).
% 1.38/0.57  fof(f278,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl5_1),
% 1.38/0.57    inference(subsumption_resolution,[],[f277,f28])).
% 1.38/0.57  fof(f28,plain,(
% 1.38/0.57    v1_relat_1(sK2)),
% 1.38/0.57    inference(cnf_transformation,[],[f18])).
% 1.38/0.57  fof(f18,plain,(
% 1.38/0.57    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 1.38/0.57  fof(f17,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f16,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.38/0.57    inference(flattening,[],[f15])).
% 1.38/0.57  fof(f15,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.38/0.57    inference(nnf_transformation,[],[f9])).
% 1.38/0.57  fof(f9,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.38/0.57    inference(flattening,[],[f8])).
% 1.38/0.57  fof(f8,plain,(
% 1.38/0.57    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.38/0.57    inference(ennf_transformation,[],[f7])).
% 1.38/0.57  fof(f7,negated_conjecture,(
% 1.38/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.38/0.57    inference(negated_conjecture,[],[f6])).
% 1.38/0.57  fof(f6,conjecture,(
% 1.38/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).
% 1.38/0.57  fof(f277,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl5_1),
% 1.38/0.57    inference(subsumption_resolution,[],[f264,f29])).
% 1.38/0.57  fof(f29,plain,(
% 1.38/0.57    v1_funct_1(sK2)),
% 1.38/0.57    inference(cnf_transformation,[],[f18])).
% 1.38/0.57  fof(f264,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl5_1),
% 1.38/0.57    inference(resolution,[],[f54,f34])).
% 1.38/0.57  fof(f34,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f20])).
% 1.38/0.57  fof(f20,plain,(
% 1.38/0.57    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(flattening,[],[f19])).
% 1.38/0.57  fof(f19,plain,(
% 1.38/0.57    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(nnf_transformation,[],[f11])).
% 1.38/0.57  fof(f11,plain,(
% 1.38/0.57    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(flattening,[],[f10])).
% 1.38/0.57  fof(f10,plain,(
% 1.38/0.57    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.38/0.57    inference(ennf_transformation,[],[f4])).
% 1.38/0.57  fof(f4,axiom,(
% 1.38/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 1.38/0.57  fof(f54,plain,(
% 1.38/0.57    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~spl5_1),
% 1.38/0.57    inference(avatar_component_clause,[],[f53])).
% 1.38/0.57  fof(f53,plain,(
% 1.38/0.57    spl5_1 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.38/0.57  fof(f276,plain,(
% 1.38/0.57    ~spl5_1 | spl5_2),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f275])).
% 1.38/0.57  fof(f275,plain,(
% 1.38/0.57    $false | (~spl5_1 | spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f274,f42])).
% 1.38/0.57  fof(f274,plain,(
% 1.38/0.57    ~v1_relat_1(k6_relat_1(sK1)) | (~spl5_1 | spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f273,f43])).
% 1.38/0.57  fof(f273,plain,(
% 1.38/0.57    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (~spl5_1 | spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f272,f28])).
% 1.38/0.57  fof(f272,plain,(
% 1.38/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (~spl5_1 | spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f271,f29])).
% 1.38/0.57  fof(f271,plain,(
% 1.38/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (~spl5_1 | spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f263,f59])).
% 1.38/0.57  fof(f59,plain,(
% 1.38/0.57    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl5_2),
% 1.38/0.57    inference(avatar_component_clause,[],[f57])).
% 1.38/0.57  fof(f57,plain,(
% 1.38/0.57    spl5_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.38/0.57  fof(f263,plain,(
% 1.38/0.57    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl5_1),
% 1.38/0.57    inference(resolution,[],[f54,f33])).
% 1.38/0.57  fof(f33,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f20])).
% 1.38/0.57  fof(f250,plain,(
% 1.38/0.57    spl5_1 | ~spl5_2 | ~spl5_3),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f249])).
% 1.38/0.57  fof(f249,plain,(
% 1.38/0.57    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.38/0.57    inference(subsumption_resolution,[],[f248,f42])).
% 1.38/0.57  fof(f248,plain,(
% 1.38/0.57    ~v1_relat_1(k6_relat_1(sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.38/0.57    inference(subsumption_resolution,[],[f241,f62])).
% 1.38/0.57  fof(f62,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl5_3),
% 1.38/0.57    inference(avatar_component_clause,[],[f61])).
% 1.38/0.57  fof(f241,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(k6_relat_1(sK1)) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(resolution,[],[f173,f48])).
% 1.38/0.57  fof(f48,plain,(
% 1.38/0.57    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.57    inference(equality_resolution,[],[f47])).
% 1.38/0.57  fof(f47,plain,(
% 1.38/0.57    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(equality_resolution,[],[f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f25])).
% 1.38/0.57  fof(f173,plain,(
% 1.38/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f172,f42])).
% 1.38/0.57  fof(f172,plain,(
% 1.38/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f165,f43])).
% 1.38/0.57  fof(f165,plain,(
% 1.38/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))) ) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(resolution,[],[f122,f44])).
% 1.38/0.57  fof(f44,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f27])).
% 1.38/0.57  fof(f122,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f121,f42])).
% 1.38/0.57  fof(f121,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(sK1)) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f120,f43])).
% 1.38/0.57  fof(f120,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f119,f28])).
% 1.38/0.57  fof(f119,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f118,f29])).
% 1.38/0.57  fof(f118,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (spl5_1 | ~spl5_2)),
% 1.38/0.57    inference(subsumption_resolution,[],[f111,f58])).
% 1.38/0.57  fof(f58,plain,(
% 1.38/0.57    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl5_2),
% 1.38/0.57    inference(avatar_component_clause,[],[f57])).
% 1.38/0.57  fof(f111,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_1),
% 1.38/0.57    inference(resolution,[],[f55,f35])).
% 1.38/0.57  fof(f35,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f20])).
% 1.38/0.57  fof(f55,plain,(
% 1.38/0.57    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | spl5_1),
% 1.38/0.57    inference(avatar_component_clause,[],[f53])).
% 1.38/0.57  fof(f66,plain,(
% 1.38/0.57    spl5_1 | spl5_2),
% 1.38/0.57    inference(avatar_split_clause,[],[f30,f57,f53])).
% 1.38/0.57  fof(f30,plain,(
% 1.38/0.57    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 1.38/0.57    inference(cnf_transformation,[],[f18])).
% 1.38/0.57  fof(f65,plain,(
% 1.38/0.57    spl5_1 | spl5_3),
% 1.38/0.57    inference(avatar_split_clause,[],[f31,f61,f53])).
% 1.38/0.57  fof(f31,plain,(
% 1.38/0.57    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 1.38/0.57    inference(cnf_transformation,[],[f18])).
% 1.38/0.57  fof(f64,plain,(
% 1.38/0.57    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.38/0.57    inference(avatar_split_clause,[],[f32,f61,f57,f53])).
% 1.38/0.57  fof(f32,plain,(
% 1.38/0.57    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 1.38/0.57    inference(cnf_transformation,[],[f18])).
% 1.38/0.57  % SZS output end Proof for theBenchmark
% 1.38/0.57  % (21780)------------------------------
% 1.38/0.57  % (21780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (21780)Termination reason: Refutation
% 1.38/0.57  
% 1.38/0.57  % (21780)Memory used [KB]: 10746
% 1.38/0.57  % (21780)Time elapsed: 0.095 s
% 1.38/0.57  % (21780)------------------------------
% 1.38/0.57  % (21780)------------------------------
% 1.38/0.57  % (21768)Success in time 0.208 s
%------------------------------------------------------------------------------
