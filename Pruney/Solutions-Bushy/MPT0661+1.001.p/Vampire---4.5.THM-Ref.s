%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0661+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:24 EST 2020

% Result     : Theorem 22.47s
% Output     : Refutation 22.47s
% Verified   : 
% Statistics : Number of formulae       :  193 (1141 expanded)
%              Number of leaves         :   24 ( 356 expanded)
%              Depth                    :   21
%              Number of atoms          :  877 (8404 expanded)
%              Number of equality atoms :  152 (2632 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f106,f138,f147,f158,f166,f3430,f4155,f4159,f66038,f66125,f66334,f76644,f76662,f78218])).

fof(f78218,plain,
    ( spl9_71
    | ~ spl9_72
    | ~ spl9_74
    | spl9_153 ),
    inference(avatar_contradiction_clause,[],[f78217])).

fof(f78217,plain,
    ( $false
    | spl9_71
    | ~ spl9_72
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f78216,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k7_relat_1(sK2,sK0)
    & ! [X3] :
        ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    & k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_relat_1(X2,X0) != X1
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relat_1(X1)) )
            & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK1 != k7_relat_1(X2,sK0)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,k1_relat_1(sK1)) )
          & k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(X2),sK0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( sK1 != k7_relat_1(X2,sK0)
        & ! [X3] :
            ( k1_funct_1(X2,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,k1_relat_1(sK1)) )
        & k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(X2),sK0)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK1 != k7_relat_1(sK2,sK0)
      & ! [X3] :
          ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
          | ~ r2_hidden(X3,k1_relat_1(sK1)) )
      & k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
                & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
             => k7_relat_1(X2,X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_funct_1)).

fof(f78216,plain,
    ( ~ v1_relat_1(sK1)
    | spl9_71
    | ~ spl9_72
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f78215,f36])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f78215,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl9_71
    | ~ spl9_72
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f78214,f3429])).

fof(f3429,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f3427])).

fof(f3427,plain,
    ( spl9_74
  <=> r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f78214,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl9_71
    | ~ spl9_72
    | spl9_153 ),
    inference(subsumption_resolution,[],[f78201,f3416])).

fof(f3416,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | spl9_71 ),
    inference(avatar_component_clause,[],[f3414])).

fof(f3414,plain,
    ( spl9_71
  <=> r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f78201,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_72
    | spl9_153 ),
    inference(superposition,[],[f69,f76681])).

fof(f76681,plain,
    ( sK4(sK2,sK0,sK1) = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | ~ spl9_72
    | spl9_153 ),
    inference(subsumption_resolution,[],[f66055,f8518])).

fof(f8518,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | spl9_153 ),
    inference(avatar_component_clause,[],[f8517])).

fof(f8517,plain,
    ( spl9_153
  <=> k1_xboole_0 = k1_funct_1(sK1,sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f66055,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | sK4(sK2,sK0,sK1) = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | ~ spl9_72 ),
    inference(resolution,[],[f3419,f1141])).

fof(f1141,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | k1_funct_1(sK1,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f1140,f73])).

fof(f73,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1140,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK1,X1) = X2
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f1139,f37])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f1139,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK1,X1) = X2
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1127,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f1127,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK1,X1) = X2
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f317,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f317,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)
      | k1_xboole_0 = k1_funct_1(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f316,f35])).

fof(f316,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)
      | k1_xboole_0 = k1_funct_1(sK1,X2)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f296,f36])).

fof(f296,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,X2) = k1_funct_1(sK2,X2)
      | k1_xboole_0 = k1_funct_1(sK1,X2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3419,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f3418])).

fof(f3418,plain,
    ( spl9_72
  <=> r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76662,plain,
    ( ~ spl9_71
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f76661,f3418,f3414])).

fof(f76661,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f70704,f41])).

fof(f41,plain,(
    sK1 != k7_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f70704,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | sK1 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f5940,f3391])).

fof(f3391,plain,(
    r2_hidden(sK3(sK2,sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f3389,f352])).

fof(f352,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f228,f73])).

fof(f228,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(X4,sK0) ) ),
    inference(superposition,[],[f71,f39])).

fof(f39,plain,(
    k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f3389,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1) ),
    inference(trivial_inequality_removal,[],[f3387])).

fof(f3387,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | sK1 != sK1 ),
    inference(resolution,[],[f162,f35])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(sK2,sK0,X0),sK0)
      | r2_hidden(k4_tarski(sK3(sK2,sK0,X0),sK4(sK2,sK0,X0)),X0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f159,f37])).

fof(f159,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(sK2,sK0,X0),sK0)
      | r2_hidden(k4_tarski(sK3(sK2,sK0,X0),sK4(sK2,sK0,X0)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f41,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f5940,plain,(
    ! [X32] :
      ( ~ r2_hidden(sK3(sK2,X32,sK1),X32)
      | ~ r2_hidden(k4_tarski(sK3(sK2,X32,sK1),sK4(sK2,X32,sK1)),sK2)
      | ~ r2_hidden(k4_tarski(sK3(sK2,X32,sK1),sK4(sK2,X32,sK1)),sK1)
      | sK1 = k7_relat_1(sK2,X32) ) ),
    inference(resolution,[],[f81,f37])).

fof(f81,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(sK3(X11,X12,sK1),sK4(X11,X12,sK1)),X11)
      | ~ r2_hidden(sK3(X11,X12,sK1),X12)
      | ~ r2_hidden(k4_tarski(sK3(X11,X12,sK1),sK4(X11,X12,sK1)),sK1)
      | sK1 = k7_relat_1(X11,X12) ) ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76644,plain,
    ( ~ spl9_2
    | ~ spl9_8
    | ~ spl9_71
    | spl9_72
    | ~ spl9_74
    | spl9_153 ),
    inference(avatar_contradiction_clause,[],[f76643])).

fof(f76643,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_71
    | spl9_72
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f76642,f69294])).

fof(f69294,plain,
    ( k1_xboole_0 != sK4(sK2,sK0,sK1)
    | ~ spl9_71
    | ~ spl9_74
    | spl9_153 ),
    inference(resolution,[],[f9230,f3415])).

fof(f3415,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ spl9_71 ),
    inference(avatar_component_clause,[],[f3414])).

fof(f9230,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK1)
        | k1_xboole_0 != X0 )
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f9229,f35])).

fof(f9229,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f9228,f36])).

fof(f9228,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_74
    | spl9_153 ),
    inference(subsumption_resolution,[],[f9223,f3429])).

fof(f9223,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK1)
        | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | spl9_153 ),
    inference(superposition,[],[f8518,f50])).

fof(f76642,plain,
    ( k1_xboole_0 = sK4(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_71
    | spl9_72 ),
    inference(subsumption_resolution,[],[f76633,f3420])).

fof(f3420,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | spl9_72 ),
    inference(avatar_component_clause,[],[f3418])).

fof(f76633,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | k1_xboole_0 = sK4(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_71 ),
    inference(superposition,[],[f13492,f65952])).

fof(f65952,plain,
    ( sK4(sK2,sK0,sK1) = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | ~ spl9_2
    | ~ spl9_71 ),
    inference(resolution,[],[f3415,f96])).

fof(f96,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(k4_tarski(X13,X14),sK1)
        | k1_funct_1(sK1,X13) = X14 )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl9_2
  <=> ! [X13,X14] :
        ( k1_funct_1(sK1,X13) = X14
        | ~ r2_hidden(k4_tarski(X13,X14),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f13492,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK2)
        | k1_xboole_0 = k1_funct_1(sK1,X0) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1130,f1143])).

fof(f1143,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f1142,f37])).

fof(f1142,plain,(
    ! [X3] :
      ( k1_xboole_0 = k1_funct_1(sK1,X3)
      | r2_hidden(X3,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1138,f38])).

fof(f1138,plain,(
    ! [X3] :
      ( k1_xboole_0 = k1_funct_1(sK1,X3)
      | r2_hidden(X3,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f1128])).

fof(f1128,plain,(
    ! [X3] :
      ( k1_xboole_0 = k1_funct_1(sK1,X3)
      | k1_xboole_0 = k1_funct_1(sK1,X3)
      | r2_hidden(X3,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f317,f68])).

fof(f1130,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_xboole_0 = k1_funct_1(sK1,X0) )
    | ~ spl9_8 ),
    inference(superposition,[],[f146,f317])).

fof(f146,plain,
    ( ! [X26] :
        ( r2_hidden(k4_tarski(X26,k1_funct_1(sK2,X26)),sK2)
        | ~ r2_hidden(X26,k1_relat_1(sK2)) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl9_8
  <=> ! [X26] :
        ( r2_hidden(k4_tarski(X26,k1_funct_1(sK2,X26)),sK2)
        | ~ r2_hidden(X26,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f66334,plain,
    ( ~ spl9_4
    | ~ spl9_74
    | ~ spl9_153
    | spl9_183 ),
    inference(avatar_contradiction_clause,[],[f66333])).

fof(f66333,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_74
    | ~ spl9_153
    | spl9_183 ),
    inference(subsumption_resolution,[],[f8569,f8916])).

fof(f8916,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK3(sK2,sK0,sK1))
    | spl9_183 ),
    inference(avatar_component_clause,[],[f8915])).

fof(f8915,plain,
    ( spl9_183
  <=> k1_xboole_0 = k1_funct_1(sK2,sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_183])])).

fof(f8569,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK3(sK2,sK0,sK1))
    | ~ spl9_4
    | ~ spl9_74
    | ~ spl9_153 ),
    inference(forward_demodulation,[],[f8558,f8519])).

fof(f8519,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | ~ spl9_153 ),
    inference(avatar_component_clause,[],[f8517])).

fof(f8558,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,sK0,sK1))
    | ~ spl9_4
    | ~ spl9_74
    | ~ spl9_153 ),
    inference(resolution,[],[f8549,f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f40,f73])).

fof(f8549,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl9_4
    | ~ spl9_74
    | ~ spl9_153 ),
    inference(subsumption_resolution,[],[f8543,f3429])).

fof(f8543,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl9_4
    | ~ spl9_153 ),
    inference(superposition,[],[f105,f8519])).

fof(f105,plain,
    ( ! [X26] :
        ( r2_hidden(k4_tarski(X26,k1_funct_1(sK1,X26)),sK1)
        | ~ r2_hidden(X26,k1_relat_1(sK1)) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_4
  <=> ! [X26] :
        ( r2_hidden(k4_tarski(X26,k1_funct_1(sK1,X26)),sK1)
        | ~ r2_hidden(X26,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f66125,plain,
    ( ~ spl9_4
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(avatar_contradiction_clause,[],[f66124])).

fof(f66124,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66123,f37])).

fof(f66123,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66122,f35])).

fof(f66122,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66121,f9731])).

fof(f9731,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl9_4
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f9725,f3429])).

fof(f9725,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl9_4
    | ~ spl9_183 ),
    inference(superposition,[],[f105,f9424])).

fof(f9424,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | ~ spl9_183 ),
    inference(duplicate_literal_removal,[],[f9421])).

fof(f9421,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK3(sK2,sK0,sK1))
    | ~ spl9_183 ),
    inference(superposition,[],[f317,f8917])).

fof(f8917,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK3(sK2,sK0,sK1))
    | ~ spl9_183 ),
    inference(avatar_component_clause,[],[f8915])).

fof(f66121,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66120,f3391])).

fof(f66120,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66119,f41])).

fof(f66119,plain,
    ( sK1 = k7_relat_1(sK2,sK0)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66109,f9431])).

fof(f9431,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f9419,f3429])).

fof(f9419,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl9_183 ),
    inference(superposition,[],[f398,f8917])).

fof(f398,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f397,f37])).

fof(f397,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f379,f38])).

fof(f379,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f229,f69])).

fof(f229,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_relat_1(sK2))
      | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f72,f39])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66109,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_183 ),
    inference(superposition,[],[f48,f66075])).

fof(f66075,plain,
    ( k1_xboole_0 = sK4(sK2,sK0,sK1)
    | ~ spl9_6
    | ~ spl9_72
    | ~ spl9_183 ),
    inference(forward_demodulation,[],[f66057,f8917])).

fof(f66057,plain,
    ( sK4(sK2,sK0,sK1) = k1_funct_1(sK2,sK3(sK2,sK0,sK1))
    | ~ spl9_6
    | ~ spl9_72 ),
    inference(resolution,[],[f3419,f137])).

fof(f137,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(k4_tarski(X13,X14),sK2)
        | k1_funct_1(sK2,X13) = X14 )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_6
  <=> ! [X13,X14] :
        ( k1_funct_1(sK2,X13) = X14
        | ~ r2_hidden(k4_tarski(X13,X14),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f66038,plain,
    ( ~ spl9_2
    | ~ spl9_4
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(avatar_contradiction_clause,[],[f66037])).

fof(f66037,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66036,f37])).

fof(f66036,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66035,f35])).

fof(f66035,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66034,f9731])).

fof(f66034,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66033,f3391])).

fof(f66033,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66032,f41])).

fof(f66032,plain,
    ( sK1 = k7_relat_1(sK2,sK0)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_71
    | ~ spl9_74
    | ~ spl9_183 ),
    inference(subsumption_resolution,[],[f66024,f9431])).

fof(f66024,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | sK1 = k7_relat_1(sK2,sK0)
    | ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_71
    | ~ spl9_183 ),
    inference(superposition,[],[f48,f65976])).

fof(f65976,plain,
    ( k1_xboole_0 = sK4(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_71
    | ~ spl9_183 ),
    inference(forward_demodulation,[],[f65952,f9424])).

fof(f4159,plain,
    ( spl9_71
    | spl9_72 ),
    inference(avatar_split_clause,[],[f4079,f3418,f3414])).

fof(f4079,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1) ),
    inference(trivial_inequality_removal,[],[f4076])).

fof(f4076,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | sK1 != sK1 ),
    inference(resolution,[],[f163,f35])).

fof(f163,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK3(sK2,sK0,X1),sK4(sK2,sK0,X1)),sK2)
      | r2_hidden(k4_tarski(sK3(sK2,sK0,X1),sK4(sK2,sK0,X1)),X1)
      | sK1 != X1 ) ),
    inference(subsumption_resolution,[],[f160,f37])).

fof(f160,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(k4_tarski(sK3(sK2,sK0,X1),sK4(sK2,sK0,X1)),sK2)
      | r2_hidden(k4_tarski(sK3(sK2,sK0,X1),sK4(sK2,sK0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f41,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4155,plain,(
    spl9_73 ),
    inference(avatar_contradiction_clause,[],[f4154])).

fof(f4154,plain,
    ( $false
    | spl9_73 ),
    inference(subsumption_resolution,[],[f4153,f37])).

fof(f4153,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_73 ),
    inference(subsumption_resolution,[],[f4152,f35])).

fof(f4152,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl9_73 ),
    inference(subsumption_resolution,[],[f4151,f3435])).

fof(f3435,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK2)
    | spl9_73 ),
    inference(resolution,[],[f3425,f73])).

fof(f3425,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | spl9_73 ),
    inference(avatar_component_clause,[],[f3423])).

fof(f3423,plain,
    ( spl9_73
  <=> r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f4151,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl9_73 ),
    inference(subsumption_resolution,[],[f4143,f41])).

fof(f4143,plain,
    ( sK1 = k7_relat_1(sK2,sK0)
    | r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl9_73 ),
    inference(resolution,[],[f3526,f47])).

fof(f3526,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK1)
    | spl9_73 ),
    inference(resolution,[],[f3432,f73])).

fof(f3432,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | spl9_73 ),
    inference(resolution,[],[f3425,f229])).

fof(f3430,plain,
    ( ~ spl9_73
    | spl9_74 ),
    inference(avatar_split_clause,[],[f3406,f3427,f3423])).

fof(f3406,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2)) ),
    inference(resolution,[],[f3391,f227])).

fof(f227,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f70,f39])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f158,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f93,f36])).

fof(f93,plain,
    ( ~ v1_funct_1(sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f147,plain,
    ( ~ spl9_5
    | spl9_8 ),
    inference(avatar_split_clause,[],[f129,f145,f132])).

fof(f129,plain,(
    ! [X26] :
      ( r2_hidden(k4_tarski(X26,k1_funct_1(sK2,X26)),sK2)
      | ~ r2_hidden(X26,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f37,f69])).

fof(f138,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f130,f136,f132])).

fof(f130,plain,(
    ! [X14,X13] :
      ( k1_funct_1(sK2,X13) = X14
      | ~ r2_hidden(k4_tarski(X13,X14),sK2)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f123,f73])).

fof(f123,plain,(
    ! [X14,X13] :
      ( k1_funct_1(sK2,X13) = X14
      | ~ r2_hidden(k4_tarski(X13,X14),sK2)
      | ~ r2_hidden(X13,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f37,f50])).

fof(f106,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f88,f104,f91])).

fof(f88,plain,(
    ! [X26] :
      ( r2_hidden(k4_tarski(X26,k1_funct_1(sK1,X26)),sK1)
      | ~ r2_hidden(X26,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f35,f69])).

fof(f97,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,(
    ! [X14,X13] :
      ( k1_funct_1(sK1,X13) = X14
      | ~ r2_hidden(k4_tarski(X13,X14),sK1)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f82,f73])).

fof(f82,plain,(
    ! [X14,X13] :
      ( k1_funct_1(sK1,X13) = X14
      | ~ r2_hidden(k4_tarski(X13,X14),sK1)
      | ~ r2_hidden(X13,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f35,f50])).

%------------------------------------------------------------------------------
