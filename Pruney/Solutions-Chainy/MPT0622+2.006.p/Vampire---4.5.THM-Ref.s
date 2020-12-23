%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 274 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :   29
%              Number of atoms          :  401 (2114 expanded)
%              Number of equality atoms :  217 (1141 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(subsumption_resolution,[],[f239,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_relat_1(sK2)
    & k1_tarski(sK0) = k2_relat_1(sK1)
    & k1_relat_1(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X2) = k1_relat_1(X1)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_relat_1(X2) = k1_tarski(sK0)
          & k1_tarski(sK0) = k2_relat_1(sK1)
          & k1_relat_1(X2) = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_relat_1(X2) = k1_tarski(sK0)
        & k1_tarski(sK0) = k2_relat_1(sK1)
        & k1_relat_1(X2) = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_relat_1(sK2)
      & k1_tarski(sK0) = k2_relat_1(sK1)
      & k1_relat_1(sK1) = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X2) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X2) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X2) = k1_relat_1(X1) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X2) = k1_relat_1(X1) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

fof(f239,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f238,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f238,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f237,f38])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f237,plain,
    ( sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f236])).

fof(f236,plain,
    ( sK1 = sK2
    | k1_relat_1(sK1) != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f223,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | sK2 = X0
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f94,f33])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | sK2 = X0
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | sK2 = X0
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f40,f35])).

fof(f35,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f223,plain,(
    ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f222,f31])).

fof(f222,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f221,f32])).

fof(f221,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f217,f38])).

fof(f217,plain,
    ( sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f215])).

fof(f215,plain,
    ( sK0 != sK0
    | k1_relat_1(sK1) != k1_relat_1(sK1)
    | sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f181,f137])).

fof(f137,plain,(
    ! [X1] :
      ( sK0 = k1_funct_1(sK1,X1)
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f132,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f75,f32])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f43,f36])).

fof(f36,plain,(
    k1_tarski(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f127,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X0 = X2
      | X1 = X2 ) ),
    inference(superposition,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X1,X2))
      | X1 = X3
      | X0 = X3
      | X2 = X3 ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X1,X2))
      | X1 = X3
      | X0 = X3
      | X0 = X3
      | X2 = X3 ) ),
    inference(superposition,[],[f68,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3))
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | X3 = X6 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK5(X0,X1,X2,X3,X4) != X3
              & sK5(X0,X1,X2,X3,X4) != X2
              & sK5(X0,X1,X2,X3,X4) != X1
              & sK5(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sK5(X0,X1,X2,X3,X4) = X3
            | sK5(X0,X1,X2,X3,X4) = X2
            | sK5(X0,X1,X2,X3,X4) = X1
            | sK5(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4) != X3
            & sK5(X0,X1,X2,X3,X4) != X2
            & sK5(X0,X1,X2,X3,X4) != X1
            & sK5(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sK5(X0,X1,X2,X3,X4) = X3
          | sK5(X0,X1,X2,X3,X4) = X2
          | sK5(X0,X1,X2,X3,X4) = X1
          | sK5(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f181,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | k1_relat_1(X2) != k1_relat_1(sK1)
      | sK2 = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f180,f95])).

fof(f180,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != k1_relat_1(sK1)
      | sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f179,f35])).

fof(f179,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | k1_relat_1(X2) != k1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f178,f33])).

fof(f178,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | k1_relat_1(X2) != k1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f170,f34])).

fof(f170,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | k1_relat_1(X2) != k1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f41,f138])).

fof(f138,plain,(
    ! [X2] :
      ( sK0 = k1_funct_1(sK2,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f132,f85])).

fof(f85,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f84,f35])).

fof(f84,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f83,f33])).

fof(f83,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f43,f37])).

fof(f37,plain,(
    k1_tarski(sK0) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (25009)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.50  % (25017)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.50  % (25001)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (25009)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (25002)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (25005)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (25003)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (25029)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (25008)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f239,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    (sK1 != sK2 & k1_tarski(sK0) = k2_relat_1(sK2) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK1 != X2 & k2_relat_1(X2) = k1_tarski(sK0) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(X2) = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X2] : (sK1 != X2 & k2_relat_1(X2) = k1_tarski(sK0) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(X2) = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_relat_1(sK2) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1)) => X1 = X2)))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1)) => X1 = X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    ~v1_relat_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f238,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f237,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    sK1 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    sK1 = sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f236])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    sK1 = sK2 | k1_relat_1(sK1) != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f223,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | sK2 = X0 | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f94,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | sK2 = X0 | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | sK2 = X0 | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(superposition,[],[f40,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f222,f31])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f221,f32])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f217,f38])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    sK1 = sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f215])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    sK0 != sK0 | k1_relat_1(sK1) != k1_relat_1(sK1) | sK1 = sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.22/0.52    inference(superposition,[],[f181,f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X1] : (sK0 = k1_funct_1(sK1,X1) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f132,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f81,f31])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f75,f32])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.52    inference(superposition,[],[f43,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    k1_tarski(sK0) = k2_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.22/0.52    inference(superposition,[],[f127,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X1 = X2) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X0 = X2 | X1 = X2) )),
% 0.22/0.52    inference(superposition,[],[f91,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X1,X2)) | X1 = X3 | X0 = X3 | X2 = X3) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X1,X2)) | X1 = X3 | X0 = X3 | X0 = X3 | X2 = X3) )),
% 0.22/0.52    inference(superposition,[],[f68,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X3,X1] : (~r2_hidden(X6,k2_enumset1(X0,X1,X2,X3)) | X2 = X6 | X1 = X6 | X0 = X6 | X3 = X6) )),
% 0.22/0.52    inference(equality_resolution,[],[f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK5(X0,X1,X2,X3,X4) != X3 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X3 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK5(X0,X1,X2,X3,X4) != X3 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X3 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(rectify,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | k1_relat_1(X2) != k1_relat_1(sK1) | sK2 = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f180,f95])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ( ! [X2] : (k1_relat_1(X2) != k1_relat_1(sK1) | sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f179,f35])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | k1_relat_1(X2) != k1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f33])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | k1_relat_1(X2) != k1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f170,f34])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | k1_relat_1(X2) != k1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.22/0.52    inference(superposition,[],[f41,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X2] : (sK0 = k1_funct_1(sK2,X2) | ~r2_hidden(X2,k1_relat_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f132,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f84,f35])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK2))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f33])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f76,f34])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(superposition,[],[f43,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    k1_tarski(sK0) = k2_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25009)------------------------------
% 0.22/0.52  % (25009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25009)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25009)Memory used [KB]: 1918
% 0.22/0.52  % (25009)Time elapsed: 0.100 s
% 0.22/0.52  % (25009)------------------------------
% 0.22/0.52  % (25009)------------------------------
% 0.22/0.53  % (25006)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (24999)Success in time 0.165 s
%------------------------------------------------------------------------------
