%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:13 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 403 expanded)
%              Number of leaves         :   16 ( 113 expanded)
%              Depth                    :   22
%              Number of atoms          :  624 (3043 expanded)
%              Number of equality atoms :   38 ( 132 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f75,f77,f193,f199,f267,f557,f563])).

fof(f563,plain,
    ( ~ spl7_4
    | spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f562,f64,f67,f188])).

fof(f188,plain,
    ( spl7_4
  <=> v1_funct_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f67,plain,
    ( spl7_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f64,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f562,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f561,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            | ~ r2_hidden(sK0,k1_relat_1(X2))
            | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
              & r2_hidden(sK0,k1_relat_1(X2)) )
            | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
          | ~ r2_hidden(sK0,k1_relat_1(X2))
          | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            & r2_hidden(sK0,k1_relat_1(X2)) )
          | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f561,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f560,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f560,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f271,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f271,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl7_1 ),
    inference(resolution,[],[f73,f119])).

fof(f119,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k1_relat_1(k5_relat_1(X6,X5)))
      | ~ v1_relat_1(X6)
      | r2_hidden(X7,k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(k5_relat_1(X6,X5)) ) ),
    inference(subsumption_resolution,[],[f115,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f115,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | r2_hidden(X7,k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ r2_hidden(X7,k1_relat_1(k5_relat_1(X6,X5)))
      | ~ v1_funct_1(k5_relat_1(X6,X5))
      | ~ v1_relat_1(k5_relat_1(X6,X5)) ) ),
    inference(resolution,[],[f104,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f104,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | r2_hidden(X8,k1_relat_1(X10))
      | ~ v1_funct_1(X10) ) ),
    inference(subsumption_resolution,[],[f99,f52])).

fof(f99,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11))
      | ~ v1_relat_1(k5_relat_1(X10,X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | r2_hidden(X8,k1_relat_1(X10))
      | ~ v1_funct_1(X10) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11))
      | ~ v1_relat_1(k5_relat_1(X10,X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | r2_hidden(X8,k1_relat_1(X10))
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f58,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f73,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f557,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f555,f33])).

fof(f555,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f554,f36])).

fof(f554,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f553,f34])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f553,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f552,f71])).

fof(f71,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f552,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f537,f35])).

fof(f537,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f466,f73])).

fof(f466,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X11,k1_relat_1(k5_relat_1(X10,X9)))
      | ~ v1_relat_1(X10)
      | r2_hidden(k1_funct_1(X10,X11),k1_relat_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f465,f52])).

fof(f465,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | r2_hidden(k1_funct_1(X10,X11),k1_relat_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v1_funct_1(X10)
      | ~ r2_hidden(X11,k1_relat_1(k5_relat_1(X10,X9)))
      | ~ v1_relat_1(k5_relat_1(X10,X9)) ) ),
    inference(subsumption_resolution,[],[f452,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f452,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | r2_hidden(k1_funct_1(X10,X11),k1_relat_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v1_funct_1(X10)
      | ~ r2_hidden(X11,k1_relat_1(k5_relat_1(X10,X9)))
      | ~ v1_funct_1(k5_relat_1(X10,X9))
      | ~ v1_relat_1(k5_relat_1(X10,X9)) ) ),
    inference(resolution,[],[f173,f61])).

fof(f173,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X10,X11),k5_relat_1(X8,X9))
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X8)
      | r2_hidden(k1_funct_1(X8,X10),k1_relat_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v1_funct_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(k1_funct_1(X8,X10),k1_relat_1(X9))
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(k4_tarski(X10,X11),k5_relat_1(X8,X9))
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(k4_tarski(X10,X11),k5_relat_1(X8,X9))
      | ~ v1_funct_1(X8) ) ),
    inference(superposition,[],[f95,f103])).

fof(f103,plain,(
    ! [X6,X4,X7,X5] :
      ( sK6(X6,X7,X4,X5) = k1_funct_1(X6,X4)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f100,f52])).

fof(f100,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | sK6(X6,X7,X4,X5) = k1_funct_1(X6,X4)
      | ~ v1_funct_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | sK6(X6,X7,X4,X5) = k1_funct_1(X6,X4)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK6(X10,X11,X8,X9),k1_relat_1(X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11))
      | ~ v1_funct_1(X11) ) ),
    inference(subsumption_resolution,[],[f90,f52])).

fof(f90,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11))
      | ~ v1_relat_1(k5_relat_1(X10,X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | r2_hidden(sK6(X10,X11,X8,X9),k1_relat_1(X11))
      | ~ v1_funct_1(X11) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11))
      | ~ v1_relat_1(k5_relat_1(X10,X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | r2_hidden(sK6(X10,X11,X8,X9),k1_relat_1(X11))
      | ~ v1_funct_1(X11)
      | ~ v1_relat_1(X11) ) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f267,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f265,f33])).

fof(f265,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f264,f34])).

fof(f264,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f261,f74])).

fof(f74,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f261,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(resolution,[],[f225,f61])).

fof(f225,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1)
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f224,f35])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f223,f36])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f221,f76])).

fof(f76,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f192,f61])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f199,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f197,f35])).

fof(f197,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f196,f36])).

fof(f196,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f195,f33])).

fof(f195,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f194,f34])).

fof(f194,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_4 ),
    inference(resolution,[],[f189,f51])).

fof(f189,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f193,plain,
    ( ~ spl7_4
    | spl7_5
    | spl7_1 ),
    inference(avatar_split_clause,[],[f186,f64,f191,f188])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_funct_1(k5_relat_1(sK2,sK1)) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_funct_1(k5_relat_1(sK2,sK1)) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f178,f33])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_funct_1(k5_relat_1(sK2,sK1)) )
    | spl7_1 ),
    inference(resolution,[],[f113,f65])).

fof(f65,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f113,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( r2_hidden(X13,k1_relat_1(k5_relat_1(X14,X12)))
      | ~ r2_hidden(k4_tarski(X13,X10),X14)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X14)
      | ~ r2_hidden(k4_tarski(X10,X11),X12)
      | ~ v1_funct_1(k5_relat_1(X14,X12)) ) ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f108,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),X12)
      | ~ r2_hidden(k4_tarski(X13,X10),X14)
      | ~ v1_relat_1(k5_relat_1(X14,X12))
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X14)
      | r2_hidden(X13,k1_relat_1(k5_relat_1(X14,X12)))
      | ~ v1_funct_1(k5_relat_1(X14,X12)) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),X12)
      | ~ r2_hidden(k4_tarski(X13,X10),X14)
      | ~ v1_relat_1(k5_relat_1(X14,X12))
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X14)
      | r2_hidden(X13,k1_relat_1(k5_relat_1(X14,X12)))
      | ~ v1_funct_1(k5_relat_1(X14,X12))
      | ~ v1_relat_1(k5_relat_1(X14,X12)) ) ),
    inference(resolution,[],[f56,f53])).

fof(f56,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f37,f67,f64])).

fof(f37,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f38,f70,f64])).

fof(f38,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f39,f70,f67,f64])).

fof(f39,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (17094)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.45  % (17092)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.45  % (17086)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (17089)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (17084)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (17091)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (17088)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (17097)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (17098)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (17102)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (17100)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (17090)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (17099)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (17085)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (17085)Refutation not found, incomplete strategy% (17085)------------------------------
% 0.21/0.51  % (17085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17085)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17085)Memory used [KB]: 10618
% 0.21/0.51  % (17085)Time elapsed: 0.076 s
% 0.21/0.51  % (17085)------------------------------
% 0.21/0.51  % (17085)------------------------------
% 0.21/0.51  % (17087)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (17101)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (17095)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (17104)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (17096)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (17104)Refutation not found, incomplete strategy% (17104)------------------------------
% 0.21/0.52  % (17104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17104)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17104)Memory used [KB]: 10618
% 0.21/0.52  % (17104)Time elapsed: 0.116 s
% 0.21/0.52  % (17104)------------------------------
% 0.21/0.52  % (17104)------------------------------
% 1.29/0.52  % (17093)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.29/0.52  % (17086)Refutation found. Thanks to Tanya!
% 1.29/0.52  % SZS status Theorem for theBenchmark
% 1.29/0.52  % SZS output start Proof for theBenchmark
% 1.29/0.52  fof(f567,plain,(
% 1.29/0.52    $false),
% 1.29/0.52    inference(avatar_sat_refutation,[],[f72,f75,f77,f193,f199,f267,f557,f563])).
% 1.29/0.52  fof(f563,plain,(
% 1.29/0.52    ~spl7_4 | spl7_2 | ~spl7_1),
% 1.29/0.52    inference(avatar_split_clause,[],[f562,f64,f67,f188])).
% 1.29/0.52  fof(f188,plain,(
% 1.29/0.52    spl7_4 <=> v1_funct_1(k5_relat_1(sK2,sK1))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.29/0.52  fof(f67,plain,(
% 1.29/0.52    spl7_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.29/0.52  fof(f64,plain,(
% 1.29/0.52    spl7_1 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.29/0.52  fof(f562,plain,(
% 1.29/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~spl7_1),
% 1.29/0.52    inference(subsumption_resolution,[],[f561,f33])).
% 1.29/0.52  fof(f33,plain,(
% 1.29/0.52    v1_relat_1(sK1)),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f23,plain,(
% 1.29/0.52    ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.29/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22,f21])).
% 1.29/0.52  fof(f21,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f22,plain,(
% 1.29/0.52    ? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f20,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.29/0.52    inference(flattening,[],[f19])).
% 1.29/0.52  fof(f19,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.29/0.52    inference(nnf_transformation,[],[f9])).
% 1.29/0.52  fof(f9,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.29/0.52    inference(flattening,[],[f8])).
% 1.29/0.52  fof(f8,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.29/0.52    inference(ennf_transformation,[],[f7])).
% 1.29/0.52  fof(f7,negated_conjecture,(
% 1.29/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.29/0.52    inference(negated_conjecture,[],[f6])).
% 1.29/0.52  fof(f6,conjecture,(
% 1.29/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 1.29/0.52  fof(f561,plain,(
% 1.29/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~spl7_1),
% 1.29/0.52    inference(subsumption_resolution,[],[f560,f36])).
% 1.29/0.52  fof(f36,plain,(
% 1.29/0.52    v1_funct_1(sK2)),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f560,plain,(
% 1.29/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~spl7_1),
% 1.29/0.52    inference(subsumption_resolution,[],[f271,f35])).
% 1.29/0.52  fof(f35,plain,(
% 1.29/0.52    v1_relat_1(sK2)),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f271,plain,(
% 1.29/0.52    ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~spl7_1),
% 1.29/0.52    inference(resolution,[],[f73,f119])).
% 1.29/0.52  fof(f119,plain,(
% 1.29/0.52    ( ! [X6,X7,X5] : (~r2_hidden(X7,k1_relat_1(k5_relat_1(X6,X5))) | ~v1_relat_1(X6) | r2_hidden(X7,k1_relat_1(X6)) | ~v1_funct_1(X6) | ~v1_relat_1(X5) | ~v1_funct_1(k5_relat_1(X6,X5))) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f115,f52])).
% 1.29/0.52  fof(f52,plain,(
% 1.29/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f16])).
% 1.29/0.52  fof(f16,plain,(
% 1.29/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(flattening,[],[f15])).
% 1.29/0.52  fof(f15,plain,(
% 1.29/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f2])).
% 1.29/0.52  fof(f2,axiom,(
% 1.29/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.29/0.52  fof(f115,plain,(
% 1.29/0.52    ( ! [X6,X7,X5] : (~v1_relat_1(X5) | ~v1_relat_1(X6) | r2_hidden(X7,k1_relat_1(X6)) | ~v1_funct_1(X6) | ~r2_hidden(X7,k1_relat_1(k5_relat_1(X6,X5))) | ~v1_funct_1(k5_relat_1(X6,X5)) | ~v1_relat_1(k5_relat_1(X6,X5))) )),
% 1.29/0.52    inference(resolution,[],[f104,f61])).
% 1.29/0.52  fof(f61,plain,(
% 1.29/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(equality_resolution,[],[f46])).
% 1.29/0.52  fof(f46,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f30,plain,(
% 1.29/0.52    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(nnf_transformation,[],[f12])).
% 1.29/0.52  fof(f12,plain,(
% 1.29/0.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(flattening,[],[f11])).
% 1.29/0.52  fof(f11,plain,(
% 1.29/0.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f3])).
% 1.29/0.52  fof(f3,axiom,(
% 1.29/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.29/0.52  fof(f104,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | r2_hidden(X8,k1_relat_1(X10)) | ~v1_funct_1(X10)) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f99,f52])).
% 1.29/0.52  fof(f99,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11)) | ~v1_relat_1(k5_relat_1(X10,X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | r2_hidden(X8,k1_relat_1(X10)) | ~v1_funct_1(X10)) )),
% 1.29/0.52    inference(duplicate_literal_removal,[],[f98])).
% 1.29/0.52  fof(f98,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11)) | ~v1_relat_1(k5_relat_1(X10,X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | r2_hidden(X8,k1_relat_1(X10)) | ~v1_funct_1(X10) | ~v1_relat_1(X10)) )),
% 1.29/0.52    inference(resolution,[],[f58,f53])).
% 1.29/0.52  fof(f53,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f32])).
% 1.29/0.52  fof(f32,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.29/0.52    inference(flattening,[],[f31])).
% 1.29/0.52  fof(f31,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.29/0.52    inference(nnf_transformation,[],[f18])).
% 1.29/0.52  fof(f18,plain,(
% 1.29/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.29/0.52    inference(flattening,[],[f17])).
% 1.29/0.52  fof(f17,plain,(
% 1.29/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.29/0.52    inference(ennf_transformation,[],[f5])).
% 1.29/0.52  fof(f5,axiom,(
% 1.29/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.29/0.52  fof(f58,plain,(
% 1.29/0.52    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(equality_resolution,[],[f40])).
% 1.29/0.52  fof(f40,plain,(
% 1.29/0.52    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f29])).
% 1.29/0.52  fof(f29,plain,(
% 1.29/0.52    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 1.29/0.52  fof(f26,plain,(
% 1.29/0.52    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f27,plain,(
% 1.29/0.52    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f28,plain,(
% 1.29/0.52    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f25,plain,(
% 1.29/0.52    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(rectify,[],[f24])).
% 1.29/0.52  fof(f24,plain,(
% 1.29/0.52    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(nnf_transformation,[],[f10])).
% 1.29/0.52  fof(f10,plain,(
% 1.29/0.52    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(ennf_transformation,[],[f1])).
% 1.29/0.52  fof(f1,axiom,(
% 1.29/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 1.29/0.52  fof(f73,plain,(
% 1.29/0.52    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~spl7_1),
% 1.29/0.52    inference(avatar_component_clause,[],[f64])).
% 1.29/0.52  fof(f557,plain,(
% 1.29/0.52    ~spl7_1 | spl7_3),
% 1.29/0.52    inference(avatar_contradiction_clause,[],[f556])).
% 1.29/0.52  fof(f556,plain,(
% 1.29/0.52    $false | (~spl7_1 | spl7_3)),
% 1.29/0.52    inference(subsumption_resolution,[],[f555,f33])).
% 1.29/0.52  fof(f555,plain,(
% 1.29/0.52    ~v1_relat_1(sK1) | (~spl7_1 | spl7_3)),
% 1.29/0.52    inference(subsumption_resolution,[],[f554,f36])).
% 1.29/0.52  fof(f554,plain,(
% 1.29/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | (~spl7_1 | spl7_3)),
% 1.29/0.52    inference(subsumption_resolution,[],[f553,f34])).
% 1.29/0.52  fof(f34,plain,(
% 1.29/0.52    v1_funct_1(sK1)),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f553,plain,(
% 1.29/0.52    ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | (~spl7_1 | spl7_3)),
% 1.29/0.52    inference(subsumption_resolution,[],[f552,f71])).
% 1.29/0.52  fof(f71,plain,(
% 1.29/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | spl7_3),
% 1.29/0.52    inference(avatar_component_clause,[],[f70])).
% 1.29/0.52  fof(f70,plain,(
% 1.29/0.52    spl7_3 <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.29/0.52  fof(f552,plain,(
% 1.29/0.52    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~spl7_1),
% 1.29/0.52    inference(subsumption_resolution,[],[f537,f35])).
% 1.29/0.52  fof(f537,plain,(
% 1.29/0.52    ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~spl7_1),
% 1.29/0.52    inference(resolution,[],[f466,f73])).
% 1.29/0.52  fof(f466,plain,(
% 1.29/0.52    ( ! [X10,X11,X9] : (~r2_hidden(X11,k1_relat_1(k5_relat_1(X10,X9))) | ~v1_relat_1(X10) | r2_hidden(k1_funct_1(X10,X11),k1_relat_1(X9)) | ~v1_funct_1(X9) | ~v1_funct_1(X10) | ~v1_relat_1(X9)) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f465,f52])).
% 1.29/0.52  fof(f465,plain,(
% 1.29/0.52    ( ! [X10,X11,X9] : (~v1_relat_1(X9) | ~v1_relat_1(X10) | r2_hidden(k1_funct_1(X10,X11),k1_relat_1(X9)) | ~v1_funct_1(X9) | ~v1_funct_1(X10) | ~r2_hidden(X11,k1_relat_1(k5_relat_1(X10,X9))) | ~v1_relat_1(k5_relat_1(X10,X9))) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f452,f51])).
% 1.29/0.52  fof(f51,plain,(
% 1.29/0.52    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f14])).
% 1.29/0.52  fof(f14,plain,(
% 1.29/0.52    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.29/0.52    inference(flattening,[],[f13])).
% 1.29/0.52  fof(f13,plain,(
% 1.29/0.52    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f4])).
% 1.29/0.52  fof(f4,axiom,(
% 1.29/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.29/0.52  fof(f452,plain,(
% 1.29/0.52    ( ! [X10,X11,X9] : (~v1_relat_1(X9) | ~v1_relat_1(X10) | r2_hidden(k1_funct_1(X10,X11),k1_relat_1(X9)) | ~v1_funct_1(X9) | ~v1_funct_1(X10) | ~r2_hidden(X11,k1_relat_1(k5_relat_1(X10,X9))) | ~v1_funct_1(k5_relat_1(X10,X9)) | ~v1_relat_1(k5_relat_1(X10,X9))) )),
% 1.29/0.52    inference(resolution,[],[f173,f61])).
% 1.29/0.52  fof(f173,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X10,X11),k5_relat_1(X8,X9)) | ~v1_relat_1(X9) | ~v1_relat_1(X8) | r2_hidden(k1_funct_1(X8,X10),k1_relat_1(X9)) | ~v1_funct_1(X9) | ~v1_funct_1(X8)) )),
% 1.29/0.52    inference(duplicate_literal_removal,[],[f170])).
% 1.29/0.52  fof(f170,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (r2_hidden(k1_funct_1(X8,X10),k1_relat_1(X9)) | ~v1_relat_1(X9) | ~v1_relat_1(X8) | ~r2_hidden(k4_tarski(X10,X11),k5_relat_1(X8,X9)) | ~v1_funct_1(X9) | ~v1_relat_1(X9) | ~v1_relat_1(X8) | ~r2_hidden(k4_tarski(X10,X11),k5_relat_1(X8,X9)) | ~v1_funct_1(X8)) )),
% 1.29/0.52    inference(superposition,[],[f95,f103])).
% 1.29/0.52  fof(f103,plain,(
% 1.29/0.52    ( ! [X6,X4,X7,X5] : (sK6(X6,X7,X4,X5) = k1_funct_1(X6,X4) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | ~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_funct_1(X6)) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f100,f52])).
% 1.29/0.52  fof(f100,plain,(
% 1.29/0.52    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | sK6(X6,X7,X4,X5) = k1_funct_1(X6,X4) | ~v1_funct_1(X6)) )),
% 1.29/0.52    inference(duplicate_literal_removal,[],[f97])).
% 1.29/0.52  fof(f97,plain,(
% 1.29/0.52    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | sK6(X6,X7,X4,X5) = k1_funct_1(X6,X4) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 1.29/0.52    inference(resolution,[],[f58,f54])).
% 1.29/0.52  fof(f54,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f32])).
% 1.29/0.52  fof(f95,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (r2_hidden(sK6(X10,X11,X8,X9),k1_relat_1(X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | ~r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11)) | ~v1_funct_1(X11)) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f90,f52])).
% 1.29/0.52  fof(f90,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11)) | ~v1_relat_1(k5_relat_1(X10,X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | r2_hidden(sK6(X10,X11,X8,X9),k1_relat_1(X11)) | ~v1_funct_1(X11)) )),
% 1.29/0.52    inference(duplicate_literal_removal,[],[f89])).
% 1.29/0.52  fof(f89,plain,(
% 1.29/0.52    ( ! [X10,X8,X11,X9] : (~r2_hidden(k4_tarski(X8,X9),k5_relat_1(X10,X11)) | ~v1_relat_1(k5_relat_1(X10,X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | r2_hidden(sK6(X10,X11,X8,X9),k1_relat_1(X11)) | ~v1_funct_1(X11) | ~v1_relat_1(X11)) )),
% 1.29/0.52    inference(resolution,[],[f57,f53])).
% 1.29/0.52  fof(f57,plain,(
% 1.29/0.52    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(equality_resolution,[],[f41])).
% 1.29/0.52  fof(f41,plain,(
% 1.29/0.52    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f29])).
% 1.29/0.52  fof(f267,plain,(
% 1.29/0.52    ~spl7_2 | ~spl7_3 | ~spl7_5),
% 1.29/0.52    inference(avatar_contradiction_clause,[],[f266])).
% 1.29/0.52  fof(f266,plain,(
% 1.29/0.52    $false | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 1.29/0.52    inference(subsumption_resolution,[],[f265,f33])).
% 1.29/0.52  fof(f265,plain,(
% 1.29/0.52    ~v1_relat_1(sK1) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 1.29/0.52    inference(subsumption_resolution,[],[f264,f34])).
% 1.29/0.52  fof(f264,plain,(
% 1.29/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 1.29/0.52    inference(subsumption_resolution,[],[f261,f74])).
% 1.29/0.52  fof(f74,plain,(
% 1.29/0.52    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~spl7_3),
% 1.29/0.52    inference(avatar_component_clause,[],[f70])).
% 1.29/0.52  fof(f261,plain,(
% 1.29/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl7_2 | ~spl7_5)),
% 1.29/0.52    inference(resolution,[],[f225,f61])).
% 1.29/0.52  fof(f225,plain,(
% 1.29/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1)) ) | (~spl7_2 | ~spl7_5)),
% 1.29/0.52    inference(subsumption_resolution,[],[f224,f35])).
% 1.29/0.52  fof(f224,plain,(
% 1.29/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1) | ~v1_relat_1(sK2)) ) | (~spl7_2 | ~spl7_5)),
% 1.29/0.52    inference(subsumption_resolution,[],[f223,f36])).
% 1.29/0.52  fof(f223,plain,(
% 1.29/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl7_2 | ~spl7_5)),
% 1.29/0.52    inference(subsumption_resolution,[],[f221,f76])).
% 1.29/0.52  fof(f76,plain,(
% 1.29/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_2),
% 1.29/0.52    inference(avatar_component_clause,[],[f67])).
% 1.29/0.52  fof(f221,plain,(
% 1.29/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_5),
% 1.29/0.52    inference(resolution,[],[f192,f61])).
% 1.29/0.52  fof(f192,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl7_5),
% 1.29/0.52    inference(avatar_component_clause,[],[f191])).
% 1.29/0.52  fof(f191,plain,(
% 1.29/0.52    spl7_5 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.29/0.52  fof(f199,plain,(
% 1.29/0.52    spl7_4),
% 1.29/0.52    inference(avatar_contradiction_clause,[],[f198])).
% 1.29/0.52  fof(f198,plain,(
% 1.29/0.52    $false | spl7_4),
% 1.29/0.52    inference(subsumption_resolution,[],[f197,f35])).
% 1.29/0.52  fof(f197,plain,(
% 1.29/0.52    ~v1_relat_1(sK2) | spl7_4),
% 1.29/0.52    inference(subsumption_resolution,[],[f196,f36])).
% 1.29/0.52  fof(f196,plain,(
% 1.29/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_4),
% 1.29/0.52    inference(subsumption_resolution,[],[f195,f33])).
% 1.29/0.52  fof(f195,plain,(
% 1.29/0.52    ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_4),
% 1.29/0.52    inference(subsumption_resolution,[],[f194,f34])).
% 1.29/0.52  fof(f194,plain,(
% 1.29/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_4),
% 1.29/0.52    inference(resolution,[],[f189,f51])).
% 1.29/0.52  fof(f189,plain,(
% 1.29/0.52    ~v1_funct_1(k5_relat_1(sK2,sK1)) | spl7_4),
% 1.29/0.52    inference(avatar_component_clause,[],[f188])).
% 1.29/0.52  fof(f193,plain,(
% 1.29/0.52    ~spl7_4 | spl7_5 | spl7_1),
% 1.29/0.52    inference(avatar_split_clause,[],[f186,f64,f191,f188])).
% 1.29/0.52  fof(f186,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))) ) | spl7_1),
% 1.29/0.52    inference(subsumption_resolution,[],[f185,f35])).
% 1.29/0.52  fof(f185,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))) ) | spl7_1),
% 1.29/0.52    inference(subsumption_resolution,[],[f178,f33])).
% 1.29/0.52  fof(f178,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))) ) | spl7_1),
% 1.29/0.52    inference(resolution,[],[f113,f65])).
% 1.29/0.52  fof(f65,plain,(
% 1.29/0.52    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | spl7_1),
% 1.29/0.52    inference(avatar_component_clause,[],[f64])).
% 1.29/0.52  fof(f113,plain,(
% 1.29/0.52    ( ! [X14,X12,X10,X13,X11] : (r2_hidden(X13,k1_relat_1(k5_relat_1(X14,X12))) | ~r2_hidden(k4_tarski(X13,X10),X14) | ~v1_relat_1(X12) | ~v1_relat_1(X14) | ~r2_hidden(k4_tarski(X10,X11),X12) | ~v1_funct_1(k5_relat_1(X14,X12))) )),
% 1.29/0.52    inference(subsumption_resolution,[],[f108,f52])).
% 1.29/0.52  fof(f108,plain,(
% 1.29/0.52    ( ! [X14,X12,X10,X13,X11] : (~r2_hidden(k4_tarski(X10,X11),X12) | ~r2_hidden(k4_tarski(X13,X10),X14) | ~v1_relat_1(k5_relat_1(X14,X12)) | ~v1_relat_1(X12) | ~v1_relat_1(X14) | r2_hidden(X13,k1_relat_1(k5_relat_1(X14,X12))) | ~v1_funct_1(k5_relat_1(X14,X12))) )),
% 1.29/0.52    inference(duplicate_literal_removal,[],[f107])).
% 1.29/0.52  fof(f107,plain,(
% 1.29/0.52    ( ! [X14,X12,X10,X13,X11] : (~r2_hidden(k4_tarski(X10,X11),X12) | ~r2_hidden(k4_tarski(X13,X10),X14) | ~v1_relat_1(k5_relat_1(X14,X12)) | ~v1_relat_1(X12) | ~v1_relat_1(X14) | r2_hidden(X13,k1_relat_1(k5_relat_1(X14,X12))) | ~v1_funct_1(k5_relat_1(X14,X12)) | ~v1_relat_1(k5_relat_1(X14,X12))) )),
% 1.29/0.52    inference(resolution,[],[f56,f53])).
% 1.29/0.52  fof(f56,plain,(
% 1.29/0.52    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(equality_resolution,[],[f42])).
% 1.29/0.52  fof(f42,plain,(
% 1.29/0.52    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f29])).
% 1.29/0.52  fof(f77,plain,(
% 1.29/0.52    spl7_1 | spl7_2),
% 1.29/0.52    inference(avatar_split_clause,[],[f37,f67,f64])).
% 1.29/0.52  fof(f37,plain,(
% 1.29/0.52    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f75,plain,(
% 1.29/0.52    spl7_1 | spl7_3),
% 1.29/0.52    inference(avatar_split_clause,[],[f38,f70,f64])).
% 1.29/0.52  fof(f38,plain,(
% 1.29/0.52    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  fof(f72,plain,(
% 1.29/0.52    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 1.29/0.52    inference(avatar_split_clause,[],[f39,f70,f67,f64])).
% 1.29/0.52  fof(f39,plain,(
% 1.29/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 1.29/0.52    inference(cnf_transformation,[],[f23])).
% 1.29/0.52  % SZS output end Proof for theBenchmark
% 1.29/0.52  % (17086)------------------------------
% 1.29/0.52  % (17086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (17086)Termination reason: Refutation
% 1.29/0.52  
% 1.29/0.52  % (17086)Memory used [KB]: 11129
% 1.29/0.52  % (17086)Time elapsed: 0.110 s
% 1.29/0.52  % (17086)------------------------------
% 1.29/0.52  % (17086)------------------------------
% 1.29/0.52  % (17103)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.29/0.52  % (17083)Success in time 0.166 s
%------------------------------------------------------------------------------
