%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 421 expanded)
%              Number of leaves         :   21 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  572 (2375 expanded)
%              Number of equality atoms :  107 ( 655 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f275,f304,f358,f368,f373,f381,f558])).

fof(f558,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | spl7_9 ),
    inference(subsumption_resolution,[],[f556,f41])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
      | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
    & r2_hidden(sK0,k2_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
        | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
      & r2_hidden(sK0,k2_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f556,plain,
    ( ~ v1_funct_1(sK1)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f555,f43])).

fof(f43,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f555,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f553,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f553,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | spl7_9 ),
    inference(resolution,[],[f240,f388])).

fof(f388,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl7_9 ),
    inference(subsumption_resolution,[],[f387,f40])).

fof(f387,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f386,f41])).

fof(f386,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f385,f42])).

fof(f42,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f385,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_9 ),
    inference(superposition,[],[f367,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f367,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_9
  <=> r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f240,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k4_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X1,k1_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f161,f139])).

fof(f139,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X5)
      | ~ v1_relat_1(X5)
      | r2_hidden(X4,k1_relat_1(k4_relat_1(X5))) ) ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X5)
      | ~ v1_relat_1(X5)
      | r2_hidden(X4,k1_relat_1(k4_relat_1(X5)))
      | ~ v1_relat_1(k4_relat_1(X5)) ) ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f82,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f66,f45])).

fof(f66,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f161,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK6(X2,X3),X3),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f156,f71])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f34,f37,f36,f35])).

fof(f35,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f156,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK6(X2,X3),X3),X2)
      | ~ r2_hidden(sK6(X2,X3),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK6(X2,X3),X3),X2)
      | ~ r2_hidden(sK6(X2,X3),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f74,f70])).

fof(f70,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f381,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f379,f40])).

fof(f379,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f377,f41])).

fof(f377,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_8 ),
    inference(resolution,[],[f114,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f114,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_8
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f373,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f371,f40])).

fof(f371,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f369,f41])).

fof(f369,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_7 ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_7
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f368,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f366,f79,f76,f116,f113,f110])).

fof(f76,plain,
    ( spl7_1
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f79,plain,
    ( spl7_2
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f366,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f365,f40])).

fof(f365,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f360,f41])).

fof(f360,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl7_2 ),
    inference(superposition,[],[f80,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f80,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f358,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f356,f43])).

fof(f356,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f355,f40])).

fof(f355,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f354,f41])).

fof(f354,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_13 ),
    inference(resolution,[],[f339,f161])).

fof(f339,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK1,sK0),sK0),sK1)
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f338,f43])).

fof(f338,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK1,sK0),sK0),sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_13 ),
    inference(equality_resolution,[],[f321])).

fof(f321,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK6(sK1,X1),sK0),sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f320,f40])).

fof(f320,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK6(sK1,X1),sK0),sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f318,f41])).

fof(f318,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK6(sK1,X1),sK0),sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_13 ),
    inference(superposition,[],[f274,f70])).

fof(f274,plain,
    ( ! [X0] :
        ( sK0 != k1_funct_1(sK1,X0)
        | ~ r2_hidden(k4_tarski(X0,sK0),sK1) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl7_13
  <=> ! [X0] :
        ( sK0 != k1_funct_1(sK1,X0)
        | ~ r2_hidden(k4_tarski(X0,sK0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f304,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f302,f42])).

fof(f302,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f301,f40])).

fof(f301,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f300,f41])).

fof(f300,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | spl7_4 ),
    inference(resolution,[],[f101,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f51,f52])).

fof(f101,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_4
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f275,plain,
    ( ~ spl7_4
    | spl7_13
    | spl7_1 ),
    inference(avatar_split_clause,[],[f271,f76,f273,f100])).

fof(f271,plain,
    ( ! [X0] :
        ( sK0 != k1_funct_1(sK1,X0)
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,sK0),sK1) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f252,f40])).

fof(f252,plain,
    ( ! [X0] :
        ( sK0 != k1_funct_1(sK1,X0)
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,sK0),sK1)
        | ~ v1_relat_1(sK1) )
    | spl7_1 ),
    inference(superposition,[],[f91,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f169,f45])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f166,f139])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ r2_hidden(X1,k1_relat_1(k4_relat_1(X0)))
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f60,f82])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f90,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f89,f41])).

fof(f89,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(superposition,[],[f77,f52])).

fof(f77,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f81,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f44,f79,f76])).

fof(f44,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (18191)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (18200)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (18205)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (18191)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f560,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f81,f275,f304,f358,f368,f373,f381,f558])).
% 0.22/0.49  fof(f558,plain,(
% 0.22/0.49    spl7_9),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f557])).
% 0.22/0.49  fof(f557,plain,(
% 0.22/0.49    $false | spl7_9),
% 0.22/0.49    inference(subsumption_resolution,[],[f556,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    (sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.22/0.49  fof(f556,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | spl7_9),
% 0.22/0.49    inference(subsumption_resolution,[],[f555,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f555,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | spl7_9),
% 0.22/0.49    inference(subsumption_resolution,[],[f553,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f553,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | spl7_9),
% 0.22/0.49    inference(resolution,[],[f240,f388])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | spl7_9),
% 0.22/0.49    inference(subsumption_resolution,[],[f387,f40])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | spl7_9),
% 0.22/0.49    inference(subsumption_resolution,[],[f386,f41])).
% 0.22/0.49  fof(f386,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_9),
% 0.22/0.49    inference(subsumption_resolution,[],[f385,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_9),
% 0.22/0.49    inference(superposition,[],[f367,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | spl7_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl7_9 <=> r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0)) | ~v1_funct_1(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f230])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(X1,k1_relat_1(k4_relat_1(X0)))) )),
% 0.22/0.49    inference(resolution,[],[f161,f139])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),X5) | ~v1_relat_1(X5) | r2_hidden(X4,k1_relat_1(k4_relat_1(X5)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f137,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),X5) | ~v1_relat_1(X5) | r2_hidden(X4,k1_relat_1(k4_relat_1(X5))) | ~v1_relat_1(k4_relat_1(X5))) )),
% 0.22/0.49    inference(resolution,[],[f82,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f45])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(rectify,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK6(X2,X3),X3),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f156,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f34,f37,f36,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(rectify,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK6(X2,X3),X3),X2) | ~r2_hidden(sK6(X2,X3),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f155])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK6(X2,X3),X3),X2) | ~r2_hidden(sK6(X2,X3),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(superposition,[],[f74,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    spl7_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f380])).
% 0.22/0.49  fof(f380,plain,(
% 0.22/0.49    $false | spl7_8),
% 0.22/0.49    inference(subsumption_resolution,[],[f379,f40])).
% 0.22/0.49  fof(f379,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl7_8),
% 0.22/0.49    inference(subsumption_resolution,[],[f377,f41])).
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_8),
% 0.22/0.49    inference(resolution,[],[f114,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~v1_funct_1(k2_funct_1(sK1)) | spl7_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl7_8 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.49  fof(f373,plain,(
% 0.22/0.49    spl7_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f372])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    $false | spl7_7),
% 0.22/0.49    inference(subsumption_resolution,[],[f371,f40])).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl7_7),
% 0.22/0.49    inference(subsumption_resolution,[],[f369,f41])).
% 0.22/0.49  fof(f369,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_7),
% 0.22/0.49    inference(resolution,[],[f111,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(sK1)) | spl7_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl7_7 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.49  fof(f368,plain,(
% 0.22/0.49    ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_1 | spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f366,f79,f76,f116,f113,f110])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl7_1 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl7_2 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f366,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl7_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f365,f40])).
% 0.22/0.49  fof(f365,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl7_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f360,f41])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl7_2),
% 0.22/0.49    inference(superposition,[],[f80,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl7_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f358,plain,(
% 0.22/0.49    ~spl7_13),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f357])).
% 0.22/0.49  fof(f357,plain,(
% 0.22/0.49    $false | ~spl7_13),
% 0.22/0.49    inference(subsumption_resolution,[],[f356,f43])).
% 0.22/0.49  fof(f356,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl7_13),
% 0.22/0.49    inference(subsumption_resolution,[],[f355,f40])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl7_13),
% 0.22/0.49    inference(subsumption_resolution,[],[f354,f41])).
% 0.22/0.49  fof(f354,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl7_13),
% 0.22/0.49    inference(resolution,[],[f339,f161])).
% 0.22/0.49  fof(f339,plain,(
% 0.22/0.49    ~r2_hidden(k4_tarski(sK6(sK1,sK0),sK0),sK1) | ~spl7_13),
% 0.22/0.49    inference(subsumption_resolution,[],[f338,f43])).
% 0.22/0.49  fof(f338,plain,(
% 0.22/0.49    ~r2_hidden(k4_tarski(sK6(sK1,sK0),sK0),sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl7_13),
% 0.22/0.49    inference(equality_resolution,[],[f321])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    ( ! [X1] : (sK0 != X1 | ~r2_hidden(k4_tarski(sK6(sK1,X1),sK0),sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl7_13),
% 0.22/0.49    inference(subsumption_resolution,[],[f320,f40])).
% 0.22/0.49  fof(f320,plain,(
% 0.22/0.49    ( ! [X1] : (sK0 != X1 | ~r2_hidden(k4_tarski(sK6(sK1,X1),sK0),sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl7_13),
% 0.22/0.49    inference(subsumption_resolution,[],[f318,f41])).
% 0.22/0.49  fof(f318,plain,(
% 0.22/0.49    ( ! [X1] : (sK0 != X1 | ~r2_hidden(k4_tarski(sK6(sK1,X1),sK0),sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl7_13),
% 0.22/0.49    inference(superposition,[],[f274,f70])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    ( ! [X0] : (sK0 != k1_funct_1(sK1,X0) | ~r2_hidden(k4_tarski(X0,sK0),sK1)) ) | ~spl7_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f273])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    spl7_13 <=> ! [X0] : (sK0 != k1_funct_1(sK1,X0) | ~r2_hidden(k4_tarski(X0,sK0),sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    spl7_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f303])).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    $false | spl7_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f302,f42])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~v2_funct_1(sK1) | spl7_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f301,f40])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl7_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f300,f41])).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1) | spl7_4),
% 0.22/0.49    inference(resolution,[],[f101,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(superposition,[],[f51,f52])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~v1_funct_1(k4_relat_1(sK1)) | spl7_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl7_4 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    ~spl7_4 | spl7_13 | spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f271,f76,f273,f100])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    ( ! [X0] : (sK0 != k1_funct_1(sK1,X0) | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,sK0),sK1)) ) | spl7_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f252,f40])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    ( ! [X0] : (sK0 != k1_funct_1(sK1,X0) | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,sK0),sK1) | ~v1_relat_1(sK1)) ) | spl7_1),
% 0.22/0.49    inference(superposition,[],[f91,f170])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~v1_funct_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f169,f45])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f166,f139])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~r2_hidden(X1,k1_relat_1(k4_relat_1(X0))) | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f60,f82])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) = X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | spl7_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f90,f40])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v1_relat_1(sK1) | spl7_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f41])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f84,f42])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 0.22/0.49    inference(superposition,[],[f77,f52])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ~spl7_1 | ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f79,f76])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18191)------------------------------
% 0.22/0.49  % (18191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18191)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18191)Memory used [KB]: 11129
% 0.22/0.49  % (18191)Time elapsed: 0.039 s
% 0.22/0.49  % (18191)------------------------------
% 0.22/0.49  % (18191)------------------------------
% 0.22/0.50  % (18188)Success in time 0.138 s
%------------------------------------------------------------------------------
