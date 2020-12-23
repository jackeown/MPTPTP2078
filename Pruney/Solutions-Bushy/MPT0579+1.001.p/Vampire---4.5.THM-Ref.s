%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:15 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 258 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   23
%              Number of atoms          :  390 (1405 expanded)
%              Number of equality atoms :   38 ( 133 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f212,f436])).

fof(f436,plain,(
    ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f434,f42])).

fof(f42,plain,(
    ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t183_relat_1)).

fof(f434,plain,
    ( r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f429,f86])).

fof(f86,plain,(
    r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),sK0) ),
    inference(resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK7(k3_xboole_0(X0,X1),X2),X1) ) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
            | ~ r2_hidden(sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK11(X0,X1,X2),X1)
              & r2_hidden(sK11(X0,X1,X2),X0) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
          | ~ r2_hidden(sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X1)
            & r2_hidden(sK11(X0,X1,X2),X0) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f429,plain,
    ( ~ r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),sK0)
    | r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
    | ~ spl12_2 ),
    inference(resolution,[],[f356,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f356,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,X0)))
        | ~ r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),X0) )
    | ~ spl12_2 ),
    inference(resolution,[],[f341,f340])).

fof(f340,plain,(
    ! [X0] :
      ( r2_hidden(sK10(sK1,sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,X0))
      | ~ r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),X0) ) ),
    inference(resolution,[],[f334,f109])).

fof(f109,plain,(
    r2_hidden(k4_tarski(sK10(sK1,sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),sK1) ),
    inference(resolution,[],[f105,f73])).

fof(f73,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f105,plain,(
    r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) ),
    inference(resolution,[],[f101,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f91,f76])).

fof(f91,plain,(
    r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k3_xboole_0(k3_xboole_0(k2_relat_1(sK1),sK0),sK0)) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f89,plain,
    ( r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k3_xboole_0(k3_xboole_0(k2_relat_1(sK1),sK0),sK0))
    | r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f88,f55])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),X0)
      | r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k3_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f86,f74])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f334,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f69,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK6(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK6(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f341,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK1,sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),X0)
        | r2_hidden(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),k10_relat_1(k4_relat_1(sK1),X0)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f336,f197])).

fof(f197,plain,(
    r2_hidden(k4_tarski(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),sK10(sK1,sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))))),k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f196,f41])).

fof(f196,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))),sK10(sK1,sK7(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))))),k4_relat_1(sK1)) ),
    inference(resolution,[],[f77,f109])).

fof(f77,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f43,f67])).

fof(f67,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f336,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(X9,X7),k4_relat_1(sK1))
        | ~ r2_hidden(X7,X8)
        | r2_hidden(X9,k10_relat_1(k4_relat_1(sK1),X8)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f69,f207])).

fof(f207,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl12_2
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f212,plain,(
    spl12_2 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl12_2 ),
    inference(subsumption_resolution,[],[f210,f41])).

fof(f210,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_2 ),
    inference(resolution,[],[f208,f43])).

fof(f208,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl12_2 ),
    inference(avatar_component_clause,[],[f206])).

%------------------------------------------------------------------------------
