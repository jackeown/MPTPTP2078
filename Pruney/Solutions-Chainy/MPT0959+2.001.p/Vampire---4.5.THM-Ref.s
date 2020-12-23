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
% DateTime   : Thu Dec  3 13:00:05 EST 2020

% Result     : Theorem 10.42s
% Output     : Refutation 10.42s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 153 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   23
%              Number of atoms          :  354 ( 803 expanded)
%              Number of equality atoms :   77 ( 209 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f922,f932])).

fof(f932,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f931])).

fof(f931,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f930,f62])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f930,plain,
    ( ~ v1_relat_1(k1_wellord2(k1_tarski(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f929,f90])).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f929,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ v1_relat_1(k1_wellord2(k1_tarski(sK0)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f928,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f928,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ v1_relat_1(k1_wellord2(k1_tarski(sK0)))
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f923])).

fof(f923,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ v1_relat_1(k1_wellord2(k1_tarski(sK0)))
    | spl7_2 ),
    inference(resolution,[],[f921,f86])).

fof(f86,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f921,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f919])).

fof(f919,plain,
    ( spl7_2
  <=> r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f922,plain,
    ( ~ spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f917,f100,f919])).

fof(f100,plain,
    ( spl7_1
  <=> k1_wellord2(k1_tarski(sK0)) = k1_tarski(k4_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f917,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0)))
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f868])).

fof(f868,plain,
    ( k1_wellord2(k1_tarski(sK0)) != k1_wellord2(k1_tarski(sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0)))
    | spl7_1 ),
    inference(superposition,[],[f102,f297])).

fof(f297,plain,(
    ! [X0] :
      ( k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))
      | ~ r2_hidden(k4_tarski(X0,X0),k1_wellord2(k1_tarski(X0))) ) ),
    inference(resolution,[],[f279,f108])).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X2))
      | k1_tarski(X2) = X1
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f279,plain,(
    ! [X2] : r1_tarski(k1_wellord2(k1_tarski(X2)),k1_tarski(k4_tarski(X2,X2))) ),
    inference(resolution,[],[f275,f90])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X0),X1)
      | r1_tarski(k1_wellord2(k1_tarski(X0)),X1) ) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X0),X1)
      | r1_tarski(k1_wellord2(k1_tarski(X0)),X1)
      | r1_tarski(k1_wellord2(k1_tarski(X0)),X1) ) ),
    inference(superposition,[],[f159,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sK2(k1_wellord2(k1_tarski(X0)),X1) = X0
      | r1_tarski(k1_wellord2(k1_tarski(X0)),X1) ) ),
    inference(resolution,[],[f137,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f136,f62])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f125,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f53,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f159,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,sK2(k1_wellord2(k1_tarski(X4)),X5)),X5)
      | r1_tarski(k1_wellord2(k1_tarski(X4)),X5) ) ),
    inference(subsumption_resolution,[],[f155,f62])).

fof(f155,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,sK2(k1_wellord2(k1_tarski(X4)),X5)),X5)
      | r1_tarski(k1_wellord2(k1_tarski(X4)),X5)
      | ~ v1_relat_1(k1_wellord2(k1_tarski(X4))) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,sK2(k1_wellord2(k1_tarski(X4)),X5)),X5)
      | r1_tarski(k1_wellord2(k1_tarski(X4)),X5)
      | ~ v1_relat_1(k1_wellord2(k1_tarski(X4)))
      | r1_tarski(k1_wellord2(k1_tarski(X4)),X5) ) ),
    inference(superposition,[],[f54,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( sK1(k1_wellord2(k1_tarski(X0)),X1) = X0
      | r1_tarski(k1_wellord2(k1_tarski(X0)),X1) ) ),
    inference(resolution,[],[f132,f91])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f124,f88])).

fof(f124,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK1(X2,X3),k3_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK1(X2,X3),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,
    ( k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).

fof(f25,plain,
    ( ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))
   => k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (8591)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (8594)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (8600)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (8610)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (8593)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (8608)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (8591)Refutation not found, incomplete strategy% (8591)------------------------------
% 0.20/0.52  % (8591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8591)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8591)Memory used [KB]: 1663
% 0.20/0.52  % (8591)Time elapsed: 0.104 s
% 0.20/0.52  % (8591)------------------------------
% 0.20/0.52  % (8591)------------------------------
% 0.20/0.52  % (8603)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (8604)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (8604)Refutation not found, incomplete strategy% (8604)------------------------------
% 0.20/0.52  % (8604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8604)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8604)Memory used [KB]: 1791
% 0.20/0.52  % (8604)Time elapsed: 0.083 s
% 0.20/0.52  % (8604)------------------------------
% 0.20/0.52  % (8604)------------------------------
% 0.20/0.52  % (8602)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (8601)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (8616)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (8608)Refutation not found, incomplete strategy% (8608)------------------------------
% 0.20/0.53  % (8608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8596)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (8617)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (8608)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8608)Memory used [KB]: 1663
% 0.20/0.53  % (8608)Time elapsed: 0.123 s
% 0.20/0.53  % (8608)------------------------------
% 0.20/0.53  % (8608)------------------------------
% 0.20/0.53  % (8590)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (8617)Refutation not found, incomplete strategy% (8617)------------------------------
% 0.20/0.53  % (8617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8617)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8617)Memory used [KB]: 6268
% 0.20/0.53  % (8617)Time elapsed: 0.130 s
% 0.20/0.53  % (8617)------------------------------
% 0.20/0.53  % (8617)------------------------------
% 0.20/0.53  % (8616)Refutation not found, incomplete strategy% (8616)------------------------------
% 0.20/0.53  % (8616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8616)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8616)Memory used [KB]: 6268
% 0.20/0.53  % (8616)Time elapsed: 0.121 s
% 0.20/0.53  % (8616)------------------------------
% 0.20/0.53  % (8616)------------------------------
% 0.20/0.53  % (8614)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (8607)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (8592)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (8595)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (8612)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (8609)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (8615)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (8613)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (8606)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (8605)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (8606)Refutation not found, incomplete strategy% (8606)------------------------------
% 0.20/0.54  % (8606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8606)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8606)Memory used [KB]: 10746
% 0.20/0.54  % (8606)Time elapsed: 0.139 s
% 0.20/0.54  % (8606)------------------------------
% 0.20/0.54  % (8606)------------------------------
% 0.20/0.54  % (8599)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (8598)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (8597)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (8619)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (8619)Refutation not found, incomplete strategy% (8619)------------------------------
% 0.20/0.55  % (8619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8619)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8619)Memory used [KB]: 1663
% 0.20/0.55  % (8619)Time elapsed: 0.150 s
% 0.20/0.55  % (8619)------------------------------
% 0.20/0.55  % (8619)------------------------------
% 0.20/0.55  % (8614)Refutation not found, incomplete strategy% (8614)------------------------------
% 0.20/0.55  % (8614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8614)Memory used [KB]: 10746
% 0.20/0.55  % (8614)Time elapsed: 0.148 s
% 0.20/0.55  % (8614)------------------------------
% 0.20/0.55  % (8614)------------------------------
% 0.20/0.55  % (8611)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (8607)Refutation not found, incomplete strategy% (8607)------------------------------
% 0.20/0.55  % (8607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8607)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8607)Memory used [KB]: 1791
% 0.20/0.55  % (8607)Time elapsed: 0.148 s
% 0.20/0.55  % (8607)------------------------------
% 0.20/0.55  % (8607)------------------------------
% 0.20/0.55  % (8618)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.16/0.65  % (8624)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.65  % (8593)Refutation not found, incomplete strategy% (8593)------------------------------
% 2.16/0.65  % (8593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (8593)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.65  
% 2.16/0.65  % (8593)Memory used [KB]: 6140
% 2.16/0.65  % (8593)Time elapsed: 0.244 s
% 2.16/0.65  % (8593)------------------------------
% 2.16/0.65  % (8593)------------------------------
% 2.16/0.65  % (8620)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.65  % (8624)Refutation not found, incomplete strategy% (8624)------------------------------
% 2.16/0.65  % (8624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (8624)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.65  
% 2.16/0.65  % (8624)Memory used [KB]: 10746
% 2.16/0.65  % (8624)Time elapsed: 0.008 s
% 2.16/0.65  % (8624)------------------------------
% 2.16/0.65  % (8624)------------------------------
% 2.16/0.67  % (8622)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.67  % (8625)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.16/0.68  % (8627)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.69  % (8626)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.69  % (8628)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.16/0.69  % (8621)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.73/0.72  % (8592)Refutation not found, incomplete strategy% (8592)------------------------------
% 2.73/0.72  % (8592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.72  % (8592)Termination reason: Refutation not found, incomplete strategy
% 2.73/0.72  
% 2.73/0.72  % (8592)Memory used [KB]: 6524
% 2.73/0.72  % (8592)Time elapsed: 0.303 s
% 2.73/0.72  % (8592)------------------------------
% 2.73/0.72  % (8592)------------------------------
% 2.73/0.73  % (8623)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.17/0.77  % (8629)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.17/0.78  % (8629)Refutation not found, incomplete strategy% (8629)------------------------------
% 3.17/0.78  % (8629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.78  % (8629)Termination reason: Refutation not found, incomplete strategy
% 3.17/0.78  
% 3.17/0.78  % (8629)Memory used [KB]: 10746
% 3.17/0.78  % (8629)Time elapsed: 0.031 s
% 3.17/0.78  % (8629)------------------------------
% 3.17/0.78  % (8629)------------------------------
% 3.17/0.81  % (8630)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.85/0.88  % (8631)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.02/0.91  % (8632)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.41/0.94  % (8596)Time limit reached!
% 4.41/0.94  % (8596)------------------------------
% 4.41/0.94  % (8596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.94  % (8596)Termination reason: Time limit
% 4.41/0.94  
% 4.41/0.94  % (8596)Memory used [KB]: 13432
% 4.41/0.94  % (8596)Time elapsed: 0.509 s
% 4.41/0.94  % (8596)------------------------------
% 4.41/0.94  % (8596)------------------------------
% 4.90/1.02  % (8597)Time limit reached!
% 4.90/1.02  % (8597)------------------------------
% 4.90/1.02  % (8597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.90/1.02  % (8597)Termination reason: Time limit
% 4.90/1.02  
% 4.90/1.02  % (8597)Memory used [KB]: 4733
% 4.90/1.02  % (8597)Time elapsed: 0.620 s
% 4.90/1.02  % (8597)------------------------------
% 4.90/1.02  % (8597)------------------------------
% 5.63/1.14  % (8633)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 5.63/1.14  % (8633)Refutation not found, incomplete strategy% (8633)------------------------------
% 5.63/1.14  % (8633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.14  % (8633)Termination reason: Refutation not found, incomplete strategy
% 5.63/1.14  
% 5.63/1.14  % (8633)Memory used [KB]: 10746
% 5.63/1.14  % (8633)Time elapsed: 0.094 s
% 5.63/1.14  % (8633)------------------------------
% 5.63/1.14  % (8633)------------------------------
% 5.63/1.16  % (8634)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 6.35/1.19  % (8626)Time limit reached!
% 6.35/1.19  % (8626)------------------------------
% 6.35/1.19  % (8626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.35/1.19  % (8626)Termination reason: Time limit
% 6.35/1.19  
% 6.35/1.19  % (8626)Memory used [KB]: 14711
% 6.35/1.19  % (8626)Time elapsed: 0.616 s
% 6.35/1.19  % (8626)------------------------------
% 6.35/1.19  % (8626)------------------------------
% 6.83/1.28  % (8635)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 7.36/1.30  % (8634)Refutation not found, incomplete strategy% (8634)------------------------------
% 7.36/1.30  % (8634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.36/1.30  % (8634)Termination reason: Refutation not found, incomplete strategy
% 7.36/1.30  
% 7.36/1.30  % (8634)Memory used [KB]: 6268
% 7.36/1.30  % (8634)Time elapsed: 0.238 s
% 7.36/1.30  % (8634)------------------------------
% 7.36/1.30  % (8634)------------------------------
% 7.36/1.33  % (8636)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 7.36/1.36  % (8622)Time limit reached!
% 7.36/1.36  % (8622)------------------------------
% 7.36/1.36  % (8622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.36/1.36  % (8622)Termination reason: Time limit
% 7.36/1.36  
% 7.36/1.36  % (8622)Memory used [KB]: 8699
% 7.36/1.36  % (8622)Time elapsed: 0.805 s
% 7.36/1.36  % (8622)------------------------------
% 7.36/1.36  % (8622)------------------------------
% 7.91/1.42  % (8635)Refutation not found, incomplete strategy% (8635)------------------------------
% 7.91/1.42  % (8635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.42  % (8635)Termination reason: Refutation not found, incomplete strategy
% 7.91/1.42  
% 7.91/1.42  % (8635)Memory used [KB]: 6268
% 7.91/1.42  % (8635)Time elapsed: 0.236 s
% 7.91/1.42  % (8635)------------------------------
% 7.91/1.42  % (8635)------------------------------
% 7.91/1.42  % (8602)Time limit reached!
% 7.91/1.42  % (8602)------------------------------
% 7.91/1.42  % (8602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.42  % (8602)Termination reason: Time limit
% 7.91/1.42  % (8602)Termination phase: Saturation
% 7.91/1.42  
% 7.91/1.42  % (8602)Memory used [KB]: 12409
% 7.91/1.42  % (8602)Time elapsed: 1.0000 s
% 7.91/1.42  % (8602)------------------------------
% 7.91/1.42  % (8602)------------------------------
% 7.91/1.46  % (8637)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 8.84/1.50  % (8638)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 9.04/1.56  % (8639)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 9.04/1.57  % (8640)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 9.86/1.63  % (8590)Time limit reached!
% 9.86/1.63  % (8590)------------------------------
% 9.86/1.63  % (8590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.86/1.63  % (8590)Termination reason: Time limit
% 9.86/1.63  % (8590)Termination phase: Saturation
% 9.86/1.63  
% 9.86/1.63  % (8590)Memory used [KB]: 4605
% 9.86/1.63  % (8590)Time elapsed: 1.200 s
% 9.86/1.63  % (8590)------------------------------
% 9.86/1.63  % (8590)------------------------------
% 10.42/1.72  % (8636)Time limit reached!
% 10.42/1.72  % (8636)------------------------------
% 10.42/1.72  % (8636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.72  % (8636)Termination reason: Time limit
% 10.42/1.72  
% 10.42/1.72  % (8636)Memory used [KB]: 9978
% 10.42/1.72  % (8636)Time elapsed: 0.512 s
% 10.42/1.72  % (8636)------------------------------
% 10.42/1.72  % (8636)------------------------------
% 10.42/1.72  % (8595)Time limit reached!
% 10.42/1.72  % (8595)------------------------------
% 10.42/1.72  % (8595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.74  % (8595)Termination reason: Time limit
% 10.42/1.74  
% 10.42/1.74  % (8595)Memory used [KB]: 6140
% 10.42/1.74  % (8595)Time elapsed: 1.317 s
% 10.42/1.74  % (8595)------------------------------
% 10.42/1.74  % (8595)------------------------------
% 10.42/1.75  % (8638)Refutation found. Thanks to Tanya!
% 10.42/1.75  % SZS status Theorem for theBenchmark
% 10.42/1.76  % SZS output start Proof for theBenchmark
% 10.42/1.76  fof(f934,plain,(
% 10.42/1.76    $false),
% 10.42/1.76    inference(avatar_sat_refutation,[],[f103,f922,f932])).
% 10.42/1.76  fof(f932,plain,(
% 10.42/1.76    spl7_2),
% 10.42/1.76    inference(avatar_contradiction_clause,[],[f931])).
% 10.42/1.76  fof(f931,plain,(
% 10.42/1.76    $false | spl7_2),
% 10.42/1.76    inference(subsumption_resolution,[],[f930,f62])).
% 10.42/1.76  fof(f62,plain,(
% 10.42/1.76    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 10.42/1.76    inference(cnf_transformation,[],[f13])).
% 10.42/1.76  fof(f13,axiom,(
% 10.42/1.76    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 10.42/1.76  fof(f930,plain,(
% 10.42/1.76    ~v1_relat_1(k1_wellord2(k1_tarski(sK0))) | spl7_2),
% 10.42/1.76    inference(subsumption_resolution,[],[f929,f90])).
% 10.42/1.76  fof(f90,plain,(
% 10.42/1.76    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 10.42/1.76    inference(equality_resolution,[],[f89])).
% 10.42/1.76  fof(f89,plain,(
% 10.42/1.76    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 10.42/1.76    inference(equality_resolution,[],[f66])).
% 10.42/1.76  fof(f66,plain,(
% 10.42/1.76    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 10.42/1.76    inference(cnf_transformation,[],[f42])).
% 10.42/1.76  fof(f42,plain,(
% 10.42/1.76    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 10.42/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 10.42/1.76  fof(f41,plain,(
% 10.42/1.76    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 10.42/1.76    introduced(choice_axiom,[])).
% 10.42/1.76  fof(f40,plain,(
% 10.42/1.76    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 10.42/1.76    inference(rectify,[],[f39])).
% 10.42/1.76  fof(f39,plain,(
% 10.42/1.76    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 10.42/1.76    inference(nnf_transformation,[],[f4])).
% 10.42/1.76  fof(f4,axiom,(
% 10.42/1.76    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 10.42/1.76  fof(f929,plain,(
% 10.42/1.76    ~r2_hidden(sK0,k1_tarski(sK0)) | ~v1_relat_1(k1_wellord2(k1_tarski(sK0))) | spl7_2),
% 10.42/1.76    inference(subsumption_resolution,[],[f928,f80])).
% 10.42/1.76  fof(f80,plain,(
% 10.42/1.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.42/1.76    inference(equality_resolution,[],[f50])).
% 10.42/1.76  fof(f50,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.42/1.76    inference(cnf_transformation,[],[f28])).
% 10.42/1.76  fof(f28,plain,(
% 10.42/1.76    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.42/1.76    inference(flattening,[],[f27])).
% 10.42/1.76  fof(f27,plain,(
% 10.42/1.76    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.42/1.76    inference(nnf_transformation,[],[f1])).
% 10.42/1.76  fof(f1,axiom,(
% 10.42/1.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.42/1.76  fof(f928,plain,(
% 10.42/1.76    ~r1_tarski(sK0,sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | ~v1_relat_1(k1_wellord2(k1_tarski(sK0))) | spl7_2),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f923])).
% 10.42/1.76  fof(f923,plain,(
% 10.42/1.76    ~r1_tarski(sK0,sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | ~v1_relat_1(k1_wellord2(k1_tarski(sK0))) | spl7_2),
% 10.42/1.76    inference(resolution,[],[f921,f86])).
% 10.42/1.76  fof(f86,plain,(
% 10.42/1.76    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 10.42/1.76    inference(equality_resolution,[],[f57])).
% 10.42/1.76  fof(f57,plain,(
% 10.42/1.76    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f37])).
% 10.42/1.76  fof(f37,plain,(
% 10.42/1.76    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 10.42/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f36])).
% 10.42/1.76  fof(f36,plain,(
% 10.42/1.76    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 10.42/1.76    introduced(choice_axiom,[])).
% 10.42/1.76  fof(f35,plain,(
% 10.42/1.76    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 10.42/1.76    inference(rectify,[],[f34])).
% 10.42/1.76  fof(f34,plain,(
% 10.42/1.76    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 10.42/1.76    inference(flattening,[],[f33])).
% 10.42/1.76  fof(f33,plain,(
% 10.42/1.76    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 10.42/1.76    inference(nnf_transformation,[],[f19])).
% 10.42/1.76  fof(f19,plain,(
% 10.42/1.76    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 10.42/1.76    inference(flattening,[],[f18])).
% 10.42/1.76  fof(f18,plain,(
% 10.42/1.76    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 10.42/1.76    inference(ennf_transformation,[],[f12])).
% 10.42/1.76  fof(f12,axiom,(
% 10.42/1.76    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 10.42/1.76  fof(f921,plain,(
% 10.42/1.76    ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0))) | spl7_2),
% 10.42/1.76    inference(avatar_component_clause,[],[f919])).
% 10.42/1.76  fof(f919,plain,(
% 10.42/1.76    spl7_2 <=> r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0)))),
% 10.42/1.76    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 10.42/1.76  fof(f922,plain,(
% 10.42/1.76    ~spl7_2 | spl7_1),
% 10.42/1.76    inference(avatar_split_clause,[],[f917,f100,f919])).
% 10.42/1.76  fof(f100,plain,(
% 10.42/1.76    spl7_1 <=> k1_wellord2(k1_tarski(sK0)) = k1_tarski(k4_tarski(sK0,sK0))),
% 10.42/1.76    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 10.42/1.76  fof(f917,plain,(
% 10.42/1.76    ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0))) | spl7_1),
% 10.42/1.76    inference(trivial_inequality_removal,[],[f868])).
% 10.42/1.76  fof(f868,plain,(
% 10.42/1.76    k1_wellord2(k1_tarski(sK0)) != k1_wellord2(k1_tarski(sK0)) | ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k1_tarski(sK0))) | spl7_1),
% 10.42/1.76    inference(superposition,[],[f102,f297])).
% 10.42/1.76  fof(f297,plain,(
% 10.42/1.76    ( ! [X0] : (k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) | ~r2_hidden(k4_tarski(X0,X0),k1_wellord2(k1_tarski(X0)))) )),
% 10.42/1.76    inference(resolution,[],[f279,f108])).
% 10.42/1.76  fof(f108,plain,(
% 10.42/1.76    ( ! [X2,X1] : (~r1_tarski(X1,k1_tarski(X2)) | k1_tarski(X2) = X1 | ~r2_hidden(X2,X1)) )),
% 10.42/1.76    inference(resolution,[],[f51,f64])).
% 10.42/1.76  fof(f64,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f38])).
% 10.42/1.76  fof(f38,plain,(
% 10.42/1.76    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 10.42/1.76    inference(nnf_transformation,[],[f8])).
% 10.42/1.76  fof(f8,axiom,(
% 10.42/1.76    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 10.42/1.76  fof(f51,plain,(
% 10.42/1.76    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f28])).
% 10.42/1.76  fof(f279,plain,(
% 10.42/1.76    ( ! [X2] : (r1_tarski(k1_wellord2(k1_tarski(X2)),k1_tarski(k4_tarski(X2,X2)))) )),
% 10.42/1.76    inference(resolution,[],[f275,f90])).
% 10.42/1.76  fof(f275,plain,(
% 10.42/1.76    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X0),X1) | r1_tarski(k1_wellord2(k1_tarski(X0)),X1)) )),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f274])).
% 10.42/1.76  fof(f274,plain,(
% 10.42/1.76    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X0),X1) | r1_tarski(k1_wellord2(k1_tarski(X0)),X1) | r1_tarski(k1_wellord2(k1_tarski(X0)),X1)) )),
% 10.42/1.76    inference(superposition,[],[f159,f138])).
% 10.42/1.76  fof(f138,plain,(
% 10.42/1.76    ( ! [X0,X1] : (sK2(k1_wellord2(k1_tarski(X0)),X1) = X0 | r1_tarski(k1_wellord2(k1_tarski(X0)),X1)) )),
% 10.42/1.76    inference(resolution,[],[f137,f91])).
% 10.42/1.76  fof(f91,plain,(
% 10.42/1.76    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 10.42/1.76    inference(equality_resolution,[],[f65])).
% 10.42/1.76  fof(f65,plain,(
% 10.42/1.76    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 10.42/1.76    inference(cnf_transformation,[],[f42])).
% 10.42/1.76  fof(f137,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 10.42/1.76    inference(subsumption_resolution,[],[f136,f62])).
% 10.42/1.76  fof(f136,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1)) )),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f135])).
% 10.42/1.76  fof(f135,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 10.42/1.76    inference(superposition,[],[f125,f88])).
% 10.42/1.76  fof(f88,plain,(
% 10.42/1.76    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 10.42/1.76    inference(equality_resolution,[],[f55])).
% 10.42/1.76  fof(f55,plain,(
% 10.42/1.76    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f37])).
% 10.42/1.76  fof(f125,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f121])).
% 10.42/1.76  fof(f121,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_relat_1(X0) | r2_hidden(sK2(X0,X1),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 10.42/1.76    inference(resolution,[],[f53,f79])).
% 10.42/1.76  fof(f79,plain,(
% 10.42/1.76    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f24])).
% 10.42/1.76  fof(f24,plain,(
% 10.42/1.76    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 10.42/1.76    inference(flattening,[],[f23])).
% 10.42/1.76  fof(f23,plain,(
% 10.42/1.76    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 10.42/1.76    inference(ennf_transformation,[],[f11])).
% 10.42/1.76  fof(f11,axiom,(
% 10.42/1.76    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 10.42/1.76  fof(f53,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f32])).
% 10.42/1.76  fof(f32,plain,(
% 10.42/1.76    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 10.42/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).
% 10.42/1.76  fof(f31,plain,(
% 10.42/1.76    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))),
% 10.42/1.76    introduced(choice_axiom,[])).
% 10.42/1.76  fof(f30,plain,(
% 10.42/1.76    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 10.42/1.76    inference(rectify,[],[f29])).
% 10.42/1.76  fof(f29,plain,(
% 10.42/1.76    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 10.42/1.76    inference(nnf_transformation,[],[f17])).
% 10.42/1.76  fof(f17,plain,(
% 10.42/1.76    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 10.42/1.76    inference(ennf_transformation,[],[f10])).
% 10.42/1.76  fof(f10,axiom,(
% 10.42/1.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 10.42/1.76  fof(f159,plain,(
% 10.42/1.76    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,sK2(k1_wellord2(k1_tarski(X4)),X5)),X5) | r1_tarski(k1_wellord2(k1_tarski(X4)),X5)) )),
% 10.42/1.76    inference(subsumption_resolution,[],[f155,f62])).
% 10.42/1.76  fof(f155,plain,(
% 10.42/1.76    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,sK2(k1_wellord2(k1_tarski(X4)),X5)),X5) | r1_tarski(k1_wellord2(k1_tarski(X4)),X5) | ~v1_relat_1(k1_wellord2(k1_tarski(X4)))) )),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f152])).
% 10.42/1.76  fof(f152,plain,(
% 10.42/1.76    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,sK2(k1_wellord2(k1_tarski(X4)),X5)),X5) | r1_tarski(k1_wellord2(k1_tarski(X4)),X5) | ~v1_relat_1(k1_wellord2(k1_tarski(X4))) | r1_tarski(k1_wellord2(k1_tarski(X4)),X5)) )),
% 10.42/1.76    inference(superposition,[],[f54,f133])).
% 10.42/1.76  fof(f133,plain,(
% 10.42/1.76    ( ! [X0,X1] : (sK1(k1_wellord2(k1_tarski(X0)),X1) = X0 | r1_tarski(k1_wellord2(k1_tarski(X0)),X1)) )),
% 10.42/1.76    inference(resolution,[],[f132,f91])).
% 10.42/1.76  fof(f132,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 10.42/1.76    inference(subsumption_resolution,[],[f131,f62])).
% 10.42/1.76  fof(f131,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1)) )),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f130])).
% 10.42/1.76  fof(f130,plain,(
% 10.42/1.76    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 10.42/1.76    inference(superposition,[],[f124,f88])).
% 10.42/1.76  fof(f124,plain,(
% 10.42/1.76    ( ! [X2,X3] : (r2_hidden(sK1(X2,X3),k3_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X2,X3)) )),
% 10.42/1.76    inference(duplicate_literal_removal,[],[f122])).
% 10.42/1.76  fof(f122,plain,(
% 10.42/1.76    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_relat_1(X2) | r2_hidden(sK1(X2,X3),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 10.42/1.76    inference(resolution,[],[f53,f78])).
% 10.42/1.76  fof(f78,plain,(
% 10.42/1.76    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f24])).
% 10.42/1.76  fof(f54,plain,(
% 10.42/1.76    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 10.42/1.76    inference(cnf_transformation,[],[f32])).
% 10.42/1.76  fof(f102,plain,(
% 10.42/1.76    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) | spl7_1),
% 10.42/1.76    inference(avatar_component_clause,[],[f100])).
% 10.42/1.76  fof(f103,plain,(
% 10.42/1.76    ~spl7_1),
% 10.42/1.76    inference(avatar_split_clause,[],[f48,f100])).
% 10.42/1.76  fof(f48,plain,(
% 10.42/1.76    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 10.42/1.76    inference(cnf_transformation,[],[f26])).
% 10.42/1.76  fof(f26,plain,(
% 10.42/1.76    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 10.42/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).
% 10.42/1.76  fof(f25,plain,(
% 10.42/1.76    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) => k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 10.42/1.76    introduced(choice_axiom,[])).
% 10.42/1.76  fof(f16,plain,(
% 10.42/1.76    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))),
% 10.42/1.76    inference(ennf_transformation,[],[f15])).
% 10.42/1.76  fof(f15,negated_conjecture,(
% 10.42/1.76    ~! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 10.42/1.76    inference(negated_conjecture,[],[f14])).
% 10.42/1.76  fof(f14,conjecture,(
% 10.42/1.76    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 10.42/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).
% 10.42/1.76  % SZS output end Proof for theBenchmark
% 10.42/1.76  % (8638)------------------------------
% 10.42/1.76  % (8638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.76  % (8638)Termination reason: Refutation
% 10.42/1.76  
% 10.42/1.76  % (8638)Memory used [KB]: 7547
% 10.42/1.76  % (8638)Time elapsed: 0.370 s
% 10.42/1.76  % (8638)------------------------------
% 10.42/1.76  % (8638)------------------------------
% 10.42/1.77  % (8589)Success in time 1.398 s
%------------------------------------------------------------------------------
